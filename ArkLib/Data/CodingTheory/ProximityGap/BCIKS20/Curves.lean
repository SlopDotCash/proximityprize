/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.UniqueDecoding
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.WeightedAgreement
import ArkLib.Data.CodingTheory.DivergenceOfSets
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ToMathlib.Polynomial.EvalExt
import ArkLib.ToMathlib.Polynomial.NatDegreeOfSum

/-!
# BCIKS20 §6 — correlated agreement over low-degree curves

This file develops the curve (parametrized-family) machinery of [BCIKS20] §6 used to lift
proximity bounds from affine lines to low-degree curves. It relates the probability that a
random curve is close to the Reed-Solomon code to the cardinality of the good-coefficient set
(`prob_close_curve_eq_card_goodCoeffsCurve_div_card` and the threshold/cardinality bounds
`goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt`,
`goodCoeffsCurve_card_bounds_of_prob_threshold`), splitting the small- and large-error regimes
(`prob_threshold_small_of_strict_johnson`, `prob_threshold_large_of_errorBound_ge_succ_const`).

The headline result `weighted_list_agreement_on_curves_implies_correlated_agreement` packages
these into correlated agreement on curves.
-/

-- Slightly above the global cap while the §6 curve machinery remains a cohesive proof module.
set_option linter.style.longFile 3300

namespace ProximityGap

-- Decidability instances are threaded through the sections for the §6 machinery;
-- several statement-level bricks do not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory ENNReal
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [DecidableEq ι] in
lemma prob_close_curve_eq_card_goodCoeffsCurve_div_card {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} (u : WordStack F (Fin (k + 1)) ι) :
    Pr_{let z ← $ᵖ F}[
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] =
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card : ℝ≥0) /
        (Fintype.card F : ℝ≥0) := by
  classical
  simpa [RS_goodCoeffsCurve] using
    (prob_uniform_eq_card_filter_div_card (F := F)
      (P := fun z : F =>
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ))

omit [Nonempty ι] [DecidableEq ι] in
lemma goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt {k deg : ℕ}
    {domain : ι ↪ F} {δ η : ℝ≥0} (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (η : ENNReal)) :
    (η : ENNReal) * (Fintype.card F : ENNReal) <
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
        ENNReal) := by
  classical
  have hPr := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := k) (deg := deg) (domain := domain) (δ := δ) u
  have hlt :
      (η : ENNReal) <
        (((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ℝ≥0) / (Fintype.card F : ℝ≥0) : ENNReal) := by
    rw [← hPr]
    exact hprob
  have hq0 : (Fintype.card F : ℝ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hlt' :
      (η : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) / (Fintype.card F : ENNReal) := by
    simpa [ENNReal.coe_div hq0, ENNReal.coe_natCast] using hlt
  exact ENNReal.mul_lt_of_lt_div hlt'

omit [Nonempty ι] [DecidableEq ι] in
/-- If a random point on the parameter curve is close with positive
probability, then the set of good coefficients is nonempty. This is the exact
cardinality information available in the closed Johnson boundary where
`errorBound = 0`. -/
lemma goodCoeffsCurve_card_pos_of_prob_gt_zero {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (0 : ENNReal)) :
    0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card := by
  classical
  have hx := goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt
    (k := k) (deg := deg) (domain := domain) (δ := δ) (η := 0) u hprob
  have hcard_pos :
      (0 : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) := by
    simpa using hx
  by_contra hcard
  have hzero :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card = 0 :=
    Nat.eq_zero_of_not_pos hcard
  simp [hzero] at hcard_pos

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F] in
private lemma finset_card_gt_of_natCast_le_ennreal_lt {α : Type} {S : Finset α}
    {m : ℕ} {x : ENNReal}
    (hm : (m : ENNReal) ≤ x) (hx : x < (S.card : ENNReal)) :
    S.card > m := by
  exact Nat.cast_lt.mp (lt_of_le_of_lt hm hx)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F] in
private lemma finset_card_ge_of_pred_natCast_le_ennreal_lt {α : Type} {S : Finset α}
    {m : ℕ} {x : ENNReal}
    (hm : ((m - 1 : ℕ) : ENNReal) ≤ x) (hx : x < (S.card : ENNReal)) :
    S.card ≥ m := by
  rcases m with _ | m
  · exact Nat.zero_le S.card
  · have hm' : (m : ENNReal) ≤ x := by
      simpa using hm
    exact Nat.succ_le_of_lt (finset_card_gt_of_natCast_le_ennreal_lt hm' hx)

omit [Nonempty ι] [DecidableEq ι] in
/-- Convert the exact ENNReal threshold obtained from the probability
calculation into the two natural cardinality bounds used by the curve assembly
bridges. -/
lemma goodCoeffsCurve_card_bounds_of_prob_threshold {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι)
    (hx :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal))
    (hsmall :
      (k : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hlarge :
      ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal)) :
    (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k ∧
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k := by
  constructor
  · exact finset_card_gt_of_natCast_le_ennreal_lt hsmall hx
  · exact finset_card_ge_of_pred_natCast_le_ennreal_lt hlarge hx

omit [DecidableEq ι] [DecidableEq F] in
/-- The easy threshold side condition follows from the standard lower bound
`|ι| / |F| ≤ errorBound`. -/
lemma prob_threshold_small_of_errorBound_ge_const {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    (_hk : 0 < k)
    (hε :
      (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤
        errorBound δ deg domain) :
    (k : ENNReal) ≤
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
        (Fintype.card F : ENNReal) := by
  have hq0 : (Fintype.card F : ℝ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hq0E : (Fintype.card F : ENNReal) ≠ 0 := by
    exact_mod_cast hq0
  have hqtop : (Fintype.card F : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hεE :
      (((Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) :
          ENNReal) ≤ (errorBound δ deg domain : ENNReal) := by
    exact_mod_cast hε
  have hn_le :
      (Fintype.card ι : ENNReal) ≤
        (errorBound δ deg domain : ENNReal) * (Fintype.card F : ENNReal) := by
    calc
      (Fintype.card ι : ENNReal)
          = (((Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) :
              ENNReal) * (Fintype.card F : ENNReal) := by
            simp [ENNReal.coe_div hq0, ENNReal.div_mul_cancel hq0E hqtop]
      _ ≤ (errorBound δ deg domain : ENNReal) * (Fintype.card F : ENNReal) :=
            mul_le_mul_left hεE _
  have hone_le_n : (1 : ENNReal) ≤ (Fintype.card ι : ENNReal) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := ι)))
  calc
    (k : ENNReal) = (k : ENNReal) * 1 := by simp
    _ ≤ (k : ENNReal) * (Fintype.card ι : ENNReal) := by
      exact mul_le_mul_right hone_le_n _
    _ ≤ (k : ENNReal) *
          ((errorBound δ deg domain : ENNReal) * (Fintype.card F : ENNReal)) := by
      exact mul_le_mul_right hn_le _
    _ = ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) := by
      rw [mul_assoc]

omit [DecidableEq ι] [DecidableEq F] in
/-- Strict Johnson-radius hypotheses imply the easy threshold side condition. -/
lemma prob_threshold_small_of_strict_johnson {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    (hk : 0 < k)
    (hdeg : 0 < deg)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    (k : ENNReal) ≤
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
        (Fintype.card F : ENNReal) := by
  exact prob_threshold_small_of_errorBound_ge_const (deg := deg) (domain := domain)
    (δ := δ) hk (DivergenceOfSets.errorBound_ge_const (deg := deg) (domain := domain) hdeg hδ)

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
/-- The large threshold side condition follows from the stronger lower bound
`(|ι| + 1) / |F| ≤ errorBound`. -/
lemma prob_threshold_large_of_errorBound_ge_succ_const {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    (hε :
      ((Fintype.card ι + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤
        errorBound δ deg domain) :
    ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
        (Fintype.card F : ENNReal) := by
  have hq0 : (Fintype.card F : ℝ≥0) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hq0E : (Fintype.card F : ENNReal) ≠ 0 := by
    exact_mod_cast hq0
  have hqtop : (Fintype.card F : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hεE :
      ((((Fintype.card ι + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) :
          ENNReal) ≤ (errorBound δ deg domain : ENNReal) := by
    exact_mod_cast hε
  have hn_le :
      ((Fintype.card ι + 1 : ℕ) : ENNReal) ≤
        (errorBound δ deg domain : ENNReal) * (Fintype.card F : ENNReal) := by
    calc
      ((Fintype.card ι + 1 : ℕ) : ENNReal)
          = ((((Fintype.card ι + 1 : ℕ) : ℝ≥0) /
              (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) *
              (Fintype.card F : ENNReal) := by
            simp [ENNReal.coe_div hq0, ENNReal.div_mul_cancel hq0E hqtop]
      _ ≤ (errorBound δ deg domain : ENNReal) * (Fintype.card F : ENNReal) :=
            mul_le_mul_left hεE _
  have hpred :
      ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
        (k : ENNReal) * ((Fintype.card ι + 1 : ℕ) : ENNReal) := by
    have hnat : ((Fintype.card ι + 1) * k : ℕ) - 1 ≤
        k * (Fintype.card ι + 1) := by
      simp [Nat.mul_comm]
    exact_mod_cast hnat
  calc
    ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal)
        ≤ (k : ENNReal) * ((Fintype.card ι + 1 : ℕ) : ENNReal) := hpred
    _ ≤ (k : ENNReal) *
          ((errorBound δ deg domain : ENNReal) * (Fintype.card F : ENNReal)) := by
      exact mul_le_mul_right hn_le _
    _ = ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) := by
      rw [mul_assoc]

omit [DecidableEq ι] [Fintype F] in
/-- Integral-weight list agreement on a sufficiently large set of curve parameters
gives correlated coordinate agreement for the input coefficient lists. This is
the curve-facing form of [BCIKS20] Lemma 7.6. -/
theorem weighted_list_agreement_on_curves_implies_correlated_agreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {μ : ι → Set.Icc (0 : ℚ) 1}
    {α : ℝ≥0}
    {M : ℕ}
    (hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ))
    {v : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (M * Fintype.card ι + 1) * (l + 1))
    (hS'_agree : ∀ z ∈ S',
      WeightedAgreement.agree μ
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x)
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x) ≥ α) :
    WeightedAgreement.mu_set μ { x : ι | ∀ i, u i x = v i x } ≥ α := by
  exact WeightedAgreement.sufficiently_large_list_agreement_on_curve_implies_correlated_agreement
    (u := u) (μ := μ) (α := α) (v := v)
    hμ hS'_card hS'_card₁ hS'_agree

omit [DecidableEq ι] [Fintype F] in
/-- The unit weight function used to view ordinary coordinate density as a
weighted agreement measure. -/
def uniformWeight : ι → Set.Icc (0 : ℚ) 1 := fun _ => ⟨1, by simp⟩

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
lemma mu_set_uniformWeight_eq_card_div (S : Finset ι) :
    WeightedAgreement.mu_set (uniformWeight (ι := ι)) S =
      (S.card : ℝ) / (Fintype.card ι : ℝ) := by
  unfold WeightedAgreement.mu_set uniformWeight
  rw [Finset.sum_const]
  simp [nsmul_eq_mul, div_eq_inv_mul]

omit [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] in
lemma agree_uniformWeight_eq_card_div (a b : ι → F) :
    WeightedAgreement.agree (uniformWeight (ι := ι)) a b =
      ((Finset.univ.filter (fun i => a i = b i)).card : ℝ) /
        (Fintype.card ι : ℝ) := by
  rw [WeightedAgreement.agree_eq_mu_set_filter]
  exact mu_set_uniformWeight_eq_card_div _

omit [DecidableEq ι] [Fintype F] in
lemma card_ge_of_uniform_mu_set_ge {S : Finset ι} {δ : ℝ≥0}
    (hS :
      WeightedAgreement.mu_set (uniformWeight (ι := ι)) S
        ≥ ((1 - δ : ℝ≥0) : ℝ)) :
    (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0) := by
  have hn_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn_pos_nat
  rw [mu_set_uniformWeight_eq_card_div] at hS
  have hS' : ((1 - δ : ℝ≥0) : ℝ) ≤
      (S.card : ℝ) / (Fintype.card ι : ℝ) := hS
  have hreal : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤
      (S.card : ℝ) := by
    rw [le_div_iff₀ hn_pos] at hS'
    simpa [mul_comm] using hS'
  rw [ge_iff_le, ← NNReal.coe_le_coe]
  rw [NNReal.coe_mul]
  exact hreal

omit [DecidableEq ι] [Field F] [Fintype F] in
lemma agree_uniformWeight_ge_one_sub_of_relDist_le {a b : ι → F} {δ : ℝ≥0}
    (hδ : δᵣ(a, b) ≤ δ) :
    WeightedAgreement.agree (uniformWeight (ι := ι)) a b ≥ ((1 - δ : ℝ≥0) : ℝ) := by
  classical
  obtain ⟨S, hS_card, hS_agree⟩ :=
    (Code.relCloseToWord_iff_exists_agreementCols a b δ).1 hδ
  let A : Finset ι := Finset.univ.filter (fun i => a i = b i)
  have hS_subset : S ⊆ A := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hS_agree i).1 hi⟩
  have hA_card : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (A.card : ℝ≥0) := by
    exact le_trans
      ((Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S.card δ).mp hS_card)
      (by exact_mod_cast Finset.card_le_card hS_subset)
  rw [agree_uniformWeight_eq_card_div]
  have hn_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hn_pos_nat
  rw [ge_iff_le, le_div_iff₀ hn_pos]
  rw [← NNReal.coe_le_coe] at hA_card
  rwa [NNReal.coe_mul] at hA_card

omit [DecidableEq ι] [Fintype F] in
/-- Unweighted corollary of Lemma 7.6: if a sufficiently large set of curve
parameters has ordinary coordinate agreement at least `1 - δ` with codeword
curves, then the coefficient words have `jointAgreement`. This packages the
weighted list-agreement theorem into the consequent shape used by correlated
agreement for curves. -/
theorem uniform_list_agreement_on_curves_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS'_agree : ∀ z ∈ S',
      WeightedAgreement.agree (uniformWeight (ι := ι))
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x)
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)
          ≥ (1 - δ : ℝ≥0)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  let μ : ι → Set.Icc (0 : ℚ) 1 := uniformWeight (ι := ι)
  let S : Finset ι := { x : ι | ∀ i, u i x = v i x }
  have hμ : ∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (1 : ℚ) := by
    intro i
    exact ⟨1, by simp [μ, uniformWeight]⟩
  have hweighted :
      WeightedAgreement.mu_set μ S ≥ ((1 - δ : ℝ≥0) : ℝ) := by
    simpa [μ, S] using
      weighted_list_agreement_on_curves_implies_correlated_agreement
        (u := u) (μ := μ) (α := 1 - δ) (M := 1)
        hμ hS'_card (by simpa using hS'_card₁) hS'_agree
  refine ⟨S, ?_, v, ?_⟩
  · exact card_ge_of_uniform_mu_set_ge hweighted
  · intro i
    refine ⟨hv i, ?_⟩
    intro x hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2 i |>.symm⟩

omit [DecidableEq ι] [Fintype F] in
/-- If a sufficiently large set of curve parameters is pointwise close to a
codeword curve, then the coefficient words have `jointAgreement`. This is the
unweighted, curve-close form needed after the list-decoding step produces
nearby codewords for many curve parameters. -/
theorem close_codeword_curves_on_large_parameter_set_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hclose : ∀ z ∈ S',
      δᵣ((fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x),
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)) ≤ δ) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact uniform_list_agreement_on_curves_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁
    (fun z hz => agree_uniformWeight_ge_one_sub_of_relDist_le (hclose z hz))

omit [DecidableEq ι] [Fintype F] in
/-- If the close codewords found at many curve parameters are evaluations of
one codeword curve, then the coefficient words have `jointAgreement`. This
isolates the exact remaining output needed from the list-decoding extraction:
the per-parameter decoded words must be assembled into a single polynomial
curve through Reed-Solomon codewords. -/
theorem decoded_polynomials_on_codeword_curve_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (P : F → Polynomial F)
    (hPcurve : ∀ z ∈ S',
      (fun x : ι => (P z).eval (domain x)) =
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x))
    (hclose : ∀ z ∈ S',
      δᵣ((fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x),
        (fun x : ι => (P z).eval (domain x))) ≤ δ) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact close_codeword_curves_on_large_parameter_set_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁
    (fun z hz => by
      simpa [hPcurve z hz] using hclose z hz)

omit [DecidableEq ι] [Fintype F] in
/-- Same bridge as `decoded_polynomials_on_codeword_curve_implies_jointAgreement`,
with the decoded-polynomial hypotheses bundled in the natural selector form:
degree bounds plus relative closeness at each selected parameter. -/
theorem decoded_polynomial_family_on_codeword_curve_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (P : F → Polynomial F)
    (hdecoded : ∀ z ∈ S',
      (P z).natDegree < deg ∧
        δᵣ((fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x),
          (fun x : ι => (P z).eval (domain x))) ≤ δ)
    (hPcurve : ∀ z ∈ S',
      (fun x : ι => (P z).eval (domain x)) =
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact decoded_polynomials_on_codeword_curve_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁ P hPcurve (fun z hz => (hdecoded z hz).2)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The two curve notations used in the Curves files agree pointwise. -/
lemma polynomialCurveEval_eq_sum_smul {k : ℕ} (u : Fin (k + 1) → ι → F) (z : F) :
    (fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x) =
      ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t := by
  funext x
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

omit [DecidableEq ι] [Fintype F] in
/-- GoodCoeffs-facing form of the decoded-family bridge: if decoded
per-parameter polynomials are close to the syntactic parameterized curve
`∑ t, z^t • u t` and assemble into one codeword curve, then the coefficient
words have `jointAgreement`. -/
theorem decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement {l : ℕ}
    {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {v : Fin (l + 2) → ι → F}
    (hv : ∀ i, v i ∈ ReedSolomon.code domain deg)
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (P : F → Polynomial F)
    (hdecoded : ∀ z ∈ S',
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
          (P z).eval ∘ domain) ≤ δ)
    (hPcurve : ∀ z ∈ S',
      (fun x : ι => (P z).eval (domain x)) =
        (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact decoded_polynomial_family_on_codeword_curve_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁ P
    (fun z hz => by
      refine ⟨(hdecoded z hz).1, ?_⟩
      have hcurve :
          (fun x => Curve.polynomialCurveEval (F := F) (A := F) u z x) =
            ∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t :=
        polynomialCurveEval_eq_sum_smul (u := u) z
      have hP :
          (fun x : ι => (P z).eval (domain x)) = (P z).eval ∘ domain := rfl
      rw [hcurve, hP]
      exact (hdecoded z hz).2)
    hPcurve

omit [DecidableEq ι] in
/-- Relative-distance form of the per-parameter decoding witness for
`RS_goodCoeffsCurve`. The GoodCoeffs file constructs a polynomial within
`floor(δ * n)` Hamming distance; this packages the same witness as
`δᵣ ≤ δ`, which is the form consumed by the list-decoding curve bridges. -/
theorem exists_rel_close_polynomial_of_mem_goodCoeffsCurve {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι) {z : F}
    (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    ∃ Pz : Polynomial F, Pz.natDegree < deg ∧
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        Pz.eval ∘ domain) ≤ δ := by
  obtain ⟨Pz, hdeg, hdist⟩ :=
    RS_exists_Pz_of_mem_goodCoeffsCurve (k := k) (deg := deg)
      (domain := domain) (δ := δ) u hz
  exact ⟨Pz, hdeg, (Code.pairRelDist_le_iff_pairDist_le
    (u := ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
    (v := Pz.eval ∘ domain) (δ := δ)).2 hdist⟩

omit [DecidableEq ι] in
/-- Choose decoded polynomials uniformly over a finite set of good curve
parameters. The resulting selector is unconstrained away from `S'`; on `S'`
it has degree `< deg` and is relatively `δ`-close to the input curve point. -/
theorem exists_decoded_polynomial_family_of_subset_goodCoeffsCurve {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι) {S' : Finset F}
    (hS' : ∀ z ∈ S', z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) :
    ∃ P : F → Polynomial F, ∀ z ∈ S',
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          (P z).eval ∘ domain) ≤ δ := by
  classical
  let P : F → Polynomial F := fun z =>
    if hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ then
      Classical.choose
        (exists_rel_close_polynomial_of_mem_goodCoeffsCurve
          (k := k) (deg := deg) (domain := domain) (δ := δ) u hz)
    else 0
  refine ⟨P, ?_⟩
  intro z hzS'
  have hzgood := hS' z hzS'
  have hspec :=
    Classical.choose_spec
      (exists_rel_close_polynomial_of_mem_goodCoeffsCurve
        (k := k) (deg := deg) (domain := domain) (δ := δ) u hzgood)
  simpa [P, hzgood] using hspec

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Assemble a decoded polynomial family into a Reed-Solomon codeword curve once the
decoded family is known to be polynomial in the curve parameter with coefficient
polynomials of degree `< deg`.

This is the algebraic assembly step consumed by the list-decoding branch: from
`P z = ∑ i, z^i A_i` it constructs the codeword stack
`v i x = A_i(domain x)`. -/
theorem decoded_family_coefficients_assemble_codeword_curve {l deg : ℕ}
    {domain : ι ↪ F}
    [NeZero deg]
    (P : F → Polynomial F)
    (A : Fin (l + 2) → Polynomial F)
    (hAdeg : ∀ i, (A i).natDegree < deg)
    {S' : Finset F}
    (hPcoeff : ∀ z ∈ S',
      P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i) :
    ∃ v : Fin (l + 2) → ι → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      ∀ z ∈ S',
        (fun x : ι => (P z).eval (domain x)) =
          (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x) := by
  classical
  let v : Fin (l + 2) → ι → F := fun i x => (A i).eval (domain x)
  refine ⟨v, ?_, ?_⟩
  · intro i
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    refine ⟨A i, hAdeg i, ?_⟩
    rfl
  · intro z hz
    funext x
    rw [hPcoeff z hz]
    simp [v, Curve.polynomialCurveEval, Polynomial.eval_finset_sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Named form of the list-decoding assembly output expected by
`subset_goodCoeffsCurve_assembled_implies_jointAgreement`.

If §5 supplies coefficient polynomials `A_i` with
`P z = ∑ i, z^i A_i` on the selected set, this theorem produces the exact
`hassemble` hypothesis consumed by the curve GoodCoeffs bridge. -/
theorem decoded_family_coefficients_has_assembly {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (A : Fin (l + 2) → Polynomial F)
    (hAdeg : ∀ i, (A i).natDegree < deg)
    (hcoeff : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ S',
          P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i) :
    ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ v : Fin (l + 2) → ι → F,
          (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
          ∀ z ∈ S',
            (fun x : ι => (P z).eval (domain x)) =
              (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x) := by
  intro P hdecoded
  exact decoded_family_coefficients_assemble_codeword_curve
    (deg := deg) (domain := domain) P A hAdeg (hcoeff P hdecoded)

omit [DecidableEq ι] in
/-- GoodCoeffs-to-joint-agreement bridge with the remaining list-decoding output
as one explicit assembly hypothesis. If a large selected set of good curve
parameters admits decoded polynomials that assemble into one curve through
Reed-Solomon codewords, then the coefficient words have `jointAgreement`. -/
theorem subset_goodCoeffsCurve_assembled_implies_jointAgreement {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS' : ∀ z ∈ S',
      z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    (hassemble : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ v : Fin (l + 2) → ι → F,
          (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
          ∀ z ∈ S',
            (fun x : ι => (P z).eval (domain x)) =
              (fun x => Curve.polynomialCurveEval (F := F) (A := F) v z x)) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  obtain ⟨P, hdecoded⟩ :=
    exists_decoded_polynomial_family_of_subset_goodCoeffsCurve
      (k := l + 1) (deg := deg) (domain := domain) (δ := δ) u hS'
  obtain ⟨v, hv, hPcurve⟩ := hassemble P hdecoded
  exact decoded_sum_polynomial_family_on_codeword_curve_implies_jointAgreement
    (u := u) (deg := deg) (domain := domain) (δ := δ) (v := v)
    hv hS'_card hS'_card₁ P hdecoded hPcurve

omit [DecidableEq ι] in
/-- GoodCoeffs-to-joint-agreement bridge where the list-decoding output is
provided as coefficient polynomials. This removes the existential assembly
hypothesis from `subset_goodCoeffsCurve_assembled_implies_jointAgreement` in the
standard case where §5 produces `P(z, X) = ∑ z^i A_i(X)`. -/
theorem subset_goodCoeffsCurve_coefficient_assembly_implies_jointAgreement {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS' : ∀ z ∈ S',
      z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    (A : Fin (l + 2) → Polynomial F)
    (hAdeg : ∀ i, (A i).natDegree < deg)
    (hcoeff : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ S',
          P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  exact subset_goodCoeffsCurve_assembled_implies_jointAgreement
    (deg := deg) (domain := domain) (δ := δ) (u := u)
    hS'_card hS'_card₁ hS'
    (decoded_family_coefficients_has_assembly
      (deg := deg) (domain := domain) (δ := δ) (u := u) A hAdeg hcoeff)

omit [Fintype F] in
private lemma coeff_zero_of_natDegree_lt {p : Polynomial F} {d j : ℕ}
    (hp : p.natDegree < d) (hj : d ≤ j) :
    p.coeff j = 0 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp hj)

omit [Fintype F] in
/-- Coefficientwise low-degree dependence on `z` assembles a decoded family as
`P z = ∑ i, z^i A_i`. This Curves-local copy keeps the bridge available to the
top curve theorem without importing `Curves.Assembly`, which would create a
cycle. -/
theorem decoded_family_coefficients_of_coeff_polys_core {l deg : ℕ} [NeZero deg]
    {S' : Finset F} {P : F → Polynomial F}
    (B : ℕ → Polynomial F)
    (hBdeg : ∀ j < deg, (B j).natDegree < l + 2)
    (hPdeg : ∀ z ∈ S', (P z).natDegree < deg)
    (hcoeff : ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    ∃ A : Fin (l + 2) → Polynomial F,
      (∀ i, (A i).natDegree < deg) ∧
        ∀ z ∈ S',
          P z = ∑ i : Fin (l + 2), Polynomial.C (z ^ (i : ℕ)) * A i := by
  classical
  let A : Fin (l + 2) → Polynomial F := fun i =>
    ∑ j ∈ Finset.range deg, Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j
  have hAdeg : ∀ i, (A i).natDegree < deg := by
    intro i
    have hdegpos : 0 < deg := Nat.pos_of_neZero deg
    refine lt_of_le_of_lt ?_ (Nat.pred_lt (Nat.ne_of_gt hdegpos))
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := Finset.range deg)
      (f := fun j => Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j)
      (n := deg - 1) ?_
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le ((B j).coeff (i : ℕ)) j).trans
      (Nat.le_pred_of_lt (Finset.mem_range.mp hj))
  refine ⟨A, hAdeg, ?_⟩
  intro z hz
  ext j
  by_cases hj : j < deg
  · rw [hcoeff z hz j hj]
    have hBsum : (B j).eval z =
        ∑ i : Fin (l + 2), (B j).coeff (i : ℕ) * z ^ (i : ℕ) := by
      have hnat := hBdeg j hj
      rw [Polynomial.eval_eq_sum_range' hnat]
      rw [← Fin.sum_univ_eq_sum_range (fun i => (B j).coeff i * z ^ i)]
    rw [hBsum, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Polynomial.coeff_C_mul]
    have hcoeffX : (A i).coeff j = (B j).coeff (i : ℕ) := by
      change (∑ x ∈ Finset.range deg,
        Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j =
          (B j).coeff (i : ℕ)
      rw [Polynomial.finset_sum_coeff]
      calc
        (∑ x ∈ Finset.range deg,
            (Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j)
            = (Polynomial.C ((B j).coeff (i : ℕ)) * Polynomial.X ^ j).coeff j := by
                exact Finset.sum_eq_single_of_mem
                  (s := Finset.range deg)
                  (f := fun x =>
                    (Polynomial.C ((B x).coeff (i : ℕ)) * Polynomial.X ^ x).coeff j)
                  j (Finset.mem_range.mpr hj)
                  (by
                    intro b hb hbj
                    have hjb : j ≠ b := fun h => hbj h.symm
                    change (Polynomial.C ((B b).coeff (i : ℕ)) * Polynomial.X ^ b).coeff j = 0
                    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
                    simp [hjb])
        _ = (B j).coeff (i : ℕ) := by
          simp [Polynomial.coeff_C_mul]
    simp [hcoeffX, mul_comm]
  · have hjge : deg ≤ j := Nat.le_of_not_gt hj
    have hPj : (P z).coeff j = 0 := coeff_zero_of_natDegree_lt (hPdeg z hz) hjge
    rw [hPj, Polynomial.finset_sum_coeff]
    symm
    refine Finset.sum_eq_zero ?_
    intro i _
    have hAj : (A i).coeff j = 0 := coeff_zero_of_natDegree_lt (hAdeg i) hjge
    rw [Polynomial.coeff_C_mul, hAj, mul_zero]

omit [DecidableEq ι] in
/-- Curves-local coefficient-polynomial bridge. It is the same consumer shape as
the assembly file, but lives in this module so the main curve theorem can use
it without an import cycle. -/
theorem subset_goodCoeffsCurve_coeff_polys_implies_jointAgreement_core {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    {S' : Finset F}
    (hS'_card : S'.card > l + 1)
    (hS'_card₁ : S'.card ≥ (Fintype.card ι + 1) * (l + 1))
    (hS' : ∀ z ∈ S',
      z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ S',
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < l + 2) ∧
            ∀ z ∈ S', ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  refine subset_goodCoeffsCurve_assembled_implies_jointAgreement
    (deg := deg) (domain := domain) (δ := δ) (u := u)
    hS'_card hS'_card₁ hS' ?_
  intro P hdecoded
  obtain ⟨B, hBdeg, hcoeff⟩ := hcoeffPoly P hdecoded
  obtain ⟨A, hAdeg, hPcoeff⟩ :=
    decoded_family_coefficients_of_coeff_polys_core
      (l := l) (deg := deg) (S' := S') (P := P) B
      hBdeg (fun z hz => (hdecoded z hz).1) hcoeff
  exact decoded_family_coefficients_assemble_codeword_curve
    (deg := deg) (domain := domain) P A hAdeg hPcoeff

omit [DecidableEq ι] in
/-- Full-good-set specialization of the Curves-local coefficient-polynomial
bridge. -/
theorem goodCoeffsCurve_coeff_polys_implies_jointAgreement_core {l deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    {u : Fin (l + 2) → ι → F}
    (hS_card :
      (RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ).card >
        l + 1)
    (hS_card₁ :
      (RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * (l + 1))
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < l + 2) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  exact subset_goodCoeffsCurve_coeff_polys_implies_jointAgreement_core
    (deg := deg) (domain := domain) (δ := δ) (u := u)
    (S' := RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u δ)
    hS_card hS_card₁ (fun z hz => hz) hcoeffPoly

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- If every domain evaluation of a decoded family is polynomial of degree `< k + 1`
in the curve parameter, then each `X`-coefficient of the decoded polynomial is
also polynomial of degree `< k + 1` in that parameter. This is the interpolation
bridge needed between the §5 pointwise output and the coefficient-polynomial
assembly theorem above. -/
theorem coeff_polys_of_eval_polys_on_domain {k deg : ℕ}
    {domain : ι ↪ F} {S : Finset F} {P : F → Polynomial F}
    (hdeg_le : deg ≤ Fintype.card ι)
    (hPdeg : ∀ z ∈ S, (P z).natDegree < deg)
    (E : ι → Polynomial F)
    (hEdeg : ∀ x, (E x).natDegree < k + 1)
    (hEval : ∀ z ∈ S, ∀ x, (P z).eval (domain x) = (E x).eval z) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ S, ∀ j < deg, (P z).coeff j = (B j).eval z := by
  classical
  let B : ℕ → Polynomial F := fun j =>
    ∑ x : ι, Polynomial.C ((Lagrange.basis (Finset.univ : Finset ι) domain x).coeff j) *
      E x
  refine ⟨B, ?_, ?_⟩
  · intro j _hj
    refine Polynomial.natDegree_sum_lt_of_forall_lt
      (s := (Finset.univ : Finset ι))
      (f := fun x =>
        Polynomial.C ((Lagrange.basis (Finset.univ : Finset ι) domain x).coeff j) *
          E x) ?_
    intro x _hx
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (hEdeg x)
  · intro z hz j _hj
    have hdegree :
        (P z).degree < ((Finset.univ : Finset ι).card : WithBot ℕ) := by
      have hnat : (P z).natDegree < (Finset.univ : Finset ι).card := by
        exact lt_of_lt_of_le (hPdeg z hz) (by simpa using hdeg_le)
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hnat)
    have hinterp :
        P z =
          Lagrange.interpolate (Finset.univ : Finset ι) domain
            (fun x => (P z).eval (domain x)) :=
      Lagrange.eq_interpolate (s := (Finset.univ : Finset ι)) (v := domain)
        domain.injective.injOn hdegree
    calc
      (P z).coeff j
          =
            (Lagrange.interpolate (Finset.univ : Finset ι) domain
              (fun x => (P z).eval (domain x))).coeff j := by
              exact congrArg (fun q : Polynomial F => q.coeff j) hinterp
      _ = (∑ x : ι,
            Polynomial.C ((P z).eval (domain x)) *
              Lagrange.basis (Finset.univ : Finset ι) domain x).coeff j := by
              rw [Lagrange.interpolate_apply]
      _ = ∑ x : ι,
            (P z).eval (domain x) *
              (Lagrange.basis (Finset.univ : Finset ι) domain x).coeff j := by
              rw [Polynomial.finset_sum_coeff]
              simp [Polynomial.coeff_C_mul]
      _ = ∑ x : ι,
            (E x).eval z *
              (Lagrange.basis (Finset.univ : Finset ι) domain x).coeff j := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              rw [hEval z hz x]
      _ = (B j).eval z := by
              simp [B, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
                mul_comm]

omit [Fintype ι] [Nonempty ι] [Fintype F] in
/-- Selected-domain version of `coeff_polys_of_eval_polys_on_domain`. It is the
interpolation bridge needed after Claim 5.11 selects only a large coordinate
subset: evaluations on any domain subset with at least `deg` points determine
all coefficients of decoded polynomials of degree `< deg`. -/
theorem coeff_polys_of_eval_polys_on_finset_domain {k deg : ℕ}
    {domain : ι ↪ F} {S : Finset F} {D : Finset ι} {P : F → Polynomial F}
    (hdeg_le : deg ≤ D.card)
    (hPdeg : ∀ z ∈ S, (P z).natDegree < deg)
    (E : D → Polynomial F)
    (hEdeg : ∀ x, (E x).natDegree < k + 1)
    (hEval : ∀ z ∈ S, ∀ x : D, (P z).eval (domain x.1) = (E x).eval z) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ S, ∀ j < deg, (P z).coeff j = (B j).eval z := by
  classical
  let B : ℕ → Polynomial F := fun j =>
    ∑ x : D, Polynomial.C ((Lagrange.basis D domain x.1).coeff j) * E x
  refine ⟨B, ?_, ?_⟩
  · intro j _hj
    refine Polynomial.natDegree_sum_lt_of_forall_lt
      (s := Finset.univ)
      (f := fun x : D =>
        Polynomial.C ((Lagrange.basis D domain x.1).coeff j) * E x) ?_
    intro x _hx
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (hEdeg x)
  · intro z hz j _hj
    have hdegree :
        (P z).degree < (D.card : WithBot ℕ) := by
      have hnat : (P z).natDegree < D.card := by
        exact lt_of_lt_of_le (hPdeg z hz) hdeg_le
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hnat)
    have hinterp :
        P z =
          Lagrange.interpolate D domain (fun x => (P z).eval (domain x)) :=
      Lagrange.eq_interpolate (s := D) (v := domain)
        domain.injective.injOn hdegree
    calc
      (P z).coeff j
          =
            (Lagrange.interpolate D domain
              (fun x => (P z).eval (domain x))).coeff j := by
              exact congrArg (fun q : Polynomial F => q.coeff j) hinterp
      _ = (∑ x ∈ D,
            Polynomial.C ((P z).eval (domain x)) *
              Lagrange.basis D domain x).coeff j := by
              rw [Lagrange.interpolate_apply]
      _ = ∑ x ∈ D,
            (P z).eval (domain x) *
              (Lagrange.basis D domain x).coeff j := by
              rw [Polynomial.finset_sum_coeff]
              simp [Polynomial.coeff_C_mul]
      _ = ∑ x : D,
            (E x).eval z *
              (Lagrange.basis D domain x.1).coeff j := by
              rw [← Finset.sum_attach D (fun x =>
                (P z).eval (domain x) * (Lagrange.basis D domain x).coeff j)]
              refine Finset.sum_congr rfl ?_
              intro x _hx
              rw [hEval z hz x]
      _ = (B j).eval z := by
              simp [B, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
                mul_comm]

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Conversely, coefficient-polynomial dependence gives pointwise
evaluation-polynomial dependence by summing the coefficient polynomials against
the fixed domain powers. -/
theorem eval_polys_of_coeff_polys_on_domain {k deg : ℕ}
    {domain : ι ↪ F} {S : Finset F} {P : F → Polynomial F}
    (hPdeg : ∀ z ∈ S, (P z).natDegree < deg)
    (B : ℕ → Polynomial F)
    (hBdeg : ∀ j < deg, (B j).natDegree < k + 1)
    (hCoeff : ∀ z ∈ S, ∀ j < deg, (P z).coeff j = (B j).eval z) :
    ∃ E : ι → Polynomial F,
      (∀ x, (E x).natDegree < k + 1) ∧
        ∀ z ∈ S, ∀ x, (P z).eval (domain x) = (E x).eval z := by
  classical
  let E : ι → Polynomial F := fun x =>
    ∑ j ∈ Finset.range deg, Polynomial.C ((domain x) ^ j) * B j
  refine ⟨E, ?_, ?_⟩
  · intro x
    refine Polynomial.natDegree_sum_lt_of_forall_lt
      (s := Finset.range deg)
      (f := fun j => Polynomial.C ((domain x) ^ j) * B j) ?_
    intro j hj
    exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _)
      (hBdeg j (Finset.mem_range.mp hj))
  · intro z hz x
    calc
      (P z).eval (domain x)
          = ∑ j ∈ Finset.range deg, (P z).coeff j * (domain x) ^ j := by
              exact Polynomial.eval_eq_sum_range' (hPdeg z hz) (domain x)
      _ = ∑ j ∈ Finset.range deg, (B j).eval z * (domain x) ^ j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [hCoeff z hz j (Finset.mem_range.mp hj)]
      _ = (E x).eval z := by
              simp [E, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
                mul_comm]

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Upgrade a canonical decoded-family evaluation witness to the universal
`hEvalPoly` shape used by the list-decoding assembly, assuming every decoded
family agrees with the canonical one on the parameter set.

This isolates the remaining uniqueness/representative bridge: §5 can construct
one family, while §6 asks for all decoded families. -/
theorem eval_polys_for_all_decoded_of_canonical_agreement {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {S : Finset F}
    {u : WordStack F (Fin (k + 1)) ι}
    (P₀ : F → Polynomial F)
    (hEval₀ : ∃ E : ι → Polynomial F,
      (∀ x, (E x).natDegree < k + 1) ∧
        ∀ z ∈ S, ∀ x, (P₀ z).eval (domain x) = (E x).eval z)
    (huniq : ∀ P : F → Polynomial F,
      (∀ z ∈ S,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ S, P z = P₀ z) :
    ∀ P : F → Polynomial F,
      (∀ z ∈ S,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ E : ι → Polynomial F,
          (∀ x, (E x).natDegree < k + 1) ∧
            ∀ z ∈ S, ∀ x, (P z).eval (domain x) = (E x).eval z := by
  intro P hdecoded
  obtain ⟨E, hEdeg, hEval⟩ := hEval₀
  refine ⟨E, hEdeg, ?_⟩
  intro z hz x
  rw [huniq P hdecoded z hz]
  exact hEval z hz x

omit [Nonempty ι] [DecidableEq ι] [Fintype F] in
/-- Coefficient-polynomial analogue of
`eval_polys_for_all_decoded_of_canonical_agreement`. -/
theorem coeff_polys_for_all_decoded_of_canonical_agreement {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {S : Finset F}
    {u : WordStack F (Fin (k + 1)) ι}
    (P₀ : F → Polynomial F)
    (hCoeff₀ : ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ S, ∀ j < deg, (P₀ z).coeff j = (B j).eval z)
    (huniq : ∀ P : F → Polynomial F,
      (∀ z ∈ S,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ S, P z = P₀ z) :
    ∀ P : F → Polynomial F,
      (∀ z ∈ S,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ S, ∀ j < deg, (P z).coeff j = (B j).eval z := by
  intro P hdecoded
  obtain ⟨B, hBdeg, hCoeff⟩ := hCoeff₀
  refine ⟨B, hBdeg, ?_⟩
  intro z hz j hj
  rw [huniq P hdecoded z hz]
  exact hCoeff z hz j hj

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Reindex a finite sum of curve coefficient words. -/
theorem curve_sum_reindex_equiv_core {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ ≃ κ') (z : F) (u : κ' → ι → F) (pow : κ' → ℕ) :
    (∑ t : κ, (z ^ pow (e t)) • u (e t)) =
      ∑ t' : κ', (z ^ pow t') • u t' := by
  simpa using (Equiv.sum_comp e (fun t' : κ' => (z ^ pow t') • u t'))

omit [Nonempty ι] [DecidableEq ι] in
/-- `RS_goodCoeffsCurve` is unchanged by a definitional reindexing of its
`Fin (k + 1)` coefficient words. -/
theorem RS_goodCoeffsCurve_finCongr_core {k k' deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    (h : k + 1 = k' + 1) (u : WordStack F (Fin (k' + 1)) ι) :
    RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain)
        (fun i => u (finCongr h i)) δ =
      RS_goodCoeffsCurve (k := k') (deg := deg) (domain := domain) u δ := by
  classical
  ext z
  have hsum :
      (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u (finCongr h t)) =
        ∑ t' : Fin (k' + 1), (z ^ (t' : ℕ)) • u t' := by
    simpa using
      (curve_sum_reindex_equiv_core (F := F) (ι := ι) (e := finCongr h) z u
        (fun t' : Fin (k' + 1) => (t' : ℕ)))
  simp only [RS_goodCoeffsCurve, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsum]

omit [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F] in
/-- `jointAgreement` is invariant under reindexing the coefficient words by an
equivalence. -/
theorem jointAgreement_reindex_equiv_core {κ κ' : Type}
    {C : Set (ι → F)} {δ : ℝ≥0}
    {W : κ → ι → F} {W' : κ' → ι → F}
    (e : κ ≃ κ')
    (hW : ∀ i x, W' (e i) x = W i x)
    (h : jointAgreement (C := C) (δ := δ) (W := W')) :
    jointAgreement (C := C) (δ := δ) (W := W) := by
  classical
  obtain ⟨S, hS_card, v', hv'⟩ := h
  refine ⟨S, hS_card, fun i => v' (e i), ?_⟩
  intro i
  constructor
  · exact (hv' (e i)).1
  · intro x hx
    have hx' := (hv' (e i)).2 hx
    rw [Finset.mem_filter] at hx' ⊢
    exact ⟨hx'.1, by simpa [hW i x] using hx'.2⟩

omit [DecidableEq ι] in
/-- Positive-`k` Curves-local coefficient-polynomial bridge. -/
theorem goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    {u : Fin (k + 1) → ι → F}
    (hS_card :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k)
    (hS_card₁ :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  let l : ℕ := k - 1
  have hlk : l + 1 = k := by omega
  have hlen : l + 2 = k + 1 := by omega
  let u' : Fin (l + 2) → ι → F := fun i => u (finCongr hlen i)
  have hgood_eq :
      RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u' δ =
        RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ := by
    simpa [u', hlk] using
      (RS_goodCoeffsCurve_finCongr_core (F := F) (ι := ι)
        (k := l + 1) (k' := k) (deg := deg) (domain := domain) (δ := δ)
        (by omega : (l + 1) + 1 = k + 1) u)
  have hja' :
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u') := by
    refine goodCoeffsCurve_coeff_polys_implies_jointAgreement_core
      (deg := deg) (domain := domain) (δ := δ) (u := u')
      ?_ ?_ ?_
    · simpa [hgood_eq, hlk] using hS_card
    · simpa [hgood_eq, hlk] using hS_card₁
    · intro P hdecoded
      have hdecoded_orig :
          ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            (P z).natDegree < deg ∧
              δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                (P z).eval ∘ domain) ≤ δ := by
        intro z hz
        have hz' :
            z ∈ RS_goodCoeffsCurve (k := l + 1) (deg := deg) (domain := domain) u' δ := by
          simpa [hgood_eq] using hz
        have hsum :
            (∑ t : Fin (l + 2), (z ^ (t : ℕ)) • u' t) =
              ∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t := by
          simpa [u'] using
            (curve_sum_reindex_equiv_core (F := F) (ι := ι) (e := finCongr hlen) z u
              (fun t : Fin (k + 1) => (t : ℕ)))
        exact ⟨(hdecoded z hz').1, by simpa [hsum] using (hdecoded z hz').2⟩
      obtain ⟨B, hBdeg, hcoeff⟩ := hcoeffPoly P hdecoded_orig
      · refine ⟨B, ?_, ?_⟩
        · intro j hj
          simpa [hlen] using hBdeg j hj
        · intro z hz j hj
          exact hcoeff z (by simpa [hgood_eq] using hz) j hj
  exact jointAgreement_reindex_equiv_core
    (F := F) (ι := ι) (C := ReedSolomon.code domain deg) (δ := δ)
    (W := u) (W' := u') (e := (finCongr hlen).symm)
    (by intro i x; simp [u'])
    hja'

omit [DecidableEq ι] in
/-- Positive-`k` Curves-local assembly bridge in the exact threshold form
produced by the probability calculation in `correlatedAgreement_affine_curves`.
-/
theorem goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_prob_threshold_core
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    {u : Fin (k + 1) → ι → F}
    (hx :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal))
    (hsmall :
      (k : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hlarge :
      ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  have hbounds :=
    goodCoeffsCurve_card_bounds_of_prob_threshold
      (deg := deg) (domain := domain) (δ := δ) u hx hsmall hlarge
  exact goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core
    (deg := deg) (domain := domain) (δ := δ) hk hbounds.1 hbounds.2 hcoeffPoly

omit [DecidableEq ι] in
/-- Positive-`k` front door when the list-decoding output is polynomial
dependence of each domain evaluation in the curve parameter. Interpolation over
the Reed-Solomon domain converts this pointwise form to coefficient-polynomial
dependence. -/
theorem goodCoeffsCurve_eval_polys_implies_jointAgreement_of_pos_core
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (hdeg_le : deg ≤ Fintype.card ι)
    {u : Fin (k + 1) → ι → F}
    (hS_card :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k)
    (hS_card₁ :
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k)
    (hEvalPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ E : ι → Polynomial F,
          (∀ x, (E x).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ x, (P z).eval (domain x) = (E x).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  refine goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_pos_core
    (deg := deg) (domain := domain) (δ := δ) hk hS_card hS_card₁ ?_
  intro P hdecoded
  obtain ⟨E, hEdeg, hEval⟩ := hEvalPoly P hdecoded
  exact coeff_polys_of_eval_polys_on_domain
    (domain := domain)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (P := P) hdeg_le (fun z hz => (hdecoded z hz).1) E hEdeg hEval

omit [DecidableEq ι] in
/-- Probability-threshold version of
`goodCoeffsCurve_eval_polys_implies_jointAgreement_of_pos_core`. -/
theorem goodCoeffsCurve_eval_polys_implies_jointAgreement_of_prob_threshold_core
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (hdeg_le : deg ≤ Fintype.card ι)
    {u : Fin (k + 1) → ι → F}
    (hx :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal))
    (hsmall :
      (k : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hlarge :
      ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hEvalPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ E : ι → Polynomial F,
          (∀ x, (E x).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ x, (P z).eval (domain x) = (E x).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  have hbounds :=
    goodCoeffsCurve_card_bounds_of_prob_threshold
      (deg := deg) (domain := domain) (δ := δ) u hx hsmall hlarge
  exact goodCoeffsCurve_eval_polys_implies_jointAgreement_of_pos_core
    (deg := deg) (domain := domain) (δ := δ) hk hdeg_le hbounds.1 hbounds.2 hEvalPoly

omit [DecidableEq ι] in
/-- List-branch front door after the probability calculation.

This packages the exact remaining outputs needed from the list-decoding part of
the argument: two lower bounds on the probability threshold and the
coefficient-polynomial extraction witness. -/
theorem RS_jointAgreement_of_prob_gt_and_coeff_polys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hsmall :
      (k : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hlarge :
      ((((Fintype.card ι + 1) * k : ℕ) - 1 : ℕ) : ENNReal) ≤
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal))
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  have hS_card :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) := by
    simpa [ENNReal.coe_mul, ENNReal.coe_natCast] using
      goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt
        (u := u) (η := (k : ℝ≥0) * errorBound δ deg domain) hprob
  exact goodCoeffsCurve_coeff_polys_implies_jointAgreement_of_prob_threshold_core
    (deg := deg) (domain := domain) (δ := δ) hk hS_card hsmall hlarge hcoeffPoly

omit [DecidableEq ι] in
/-- List-branch front door with the probability-threshold lower bounds stated
as lower bounds on `errorBound` itself. This removes the ENNReal/cardinality
arithmetic from the final list-decoding call. -/
theorem RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hεsmall :
      (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤
        errorBound δ deg domain)
    (hεlarge :
      ((Fintype.card ι + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤
        errorBound δ deg domain)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact RS_jointAgreement_of_prob_gt_and_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hk u hprob
    (prob_threshold_small_of_errorBound_ge_const
      (deg := deg) (domain := domain) (δ := δ) hk hεsmall)
    (prob_threshold_large_of_errorBound_ge_succ_const
      (deg := deg) (domain := domain) (δ := δ) hεlarge)
    hcoeffPoly

omit [DecidableEq ι] in
/-- List-branch front door with evaluation-polynomial dependence and the
probability-threshold side conditions stated as lower bounds on `errorBound`.
This is the evaluation-polynomial analogue of
`RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds`. -/
theorem RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds_eval_polys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (hdeg_le : deg ≤ Fintype.card ι)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hεsmall :
      (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤
        errorBound δ deg domain)
    (hεlarge :
      ((Fintype.card ι + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤
        errorBound δ deg domain)
    (hEvalPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ E : ι → Polynomial F,
          (∀ x, (E x).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ x, (P z).eval (domain x) = (E x).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  classical
  have hS_card :
      ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) *
          (Fintype.card F : ENNReal) <
        ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card :
          ENNReal) := by
    simpa [ENNReal.coe_mul, ENNReal.coe_natCast] using
      goodCoeffsCurve_threshold_mul_card_lt_card_of_prob_gt
        (u := u) (η := (k : ℝ≥0) * errorBound δ deg domain) hprob
  exact goodCoeffsCurve_eval_polys_implies_jointAgreement_of_prob_threshold_core
    (deg := deg) (domain := domain) (δ := δ) hk hdeg_le hS_card
    (prob_threshold_small_of_errorBound_ge_const
      (deg := deg) (domain := domain) (δ := δ) hk hεsmall)
    (prob_threshold_large_of_errorBound_ge_succ_const
      (deg := deg) (domain := domain) (δ := δ) hεlarge)
    hEvalPoly

omit [DecidableEq ι] [DecidableEq F] in
/-- In the strict Johnson branch, the Johnson expression defining
`errorBound` is large enough for the successor threshold
`(|ι| + 1) / |F|`. This is the threshold used by the coefficient-polynomial
assembly bridge. -/
theorem errorBound_ge_succ_const_of_strict_johnson {deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg]
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    ((Fintype.card ι + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤
      errorBound δ deg domain := by
  classical
  let hdeg : 0 < deg := Nat.pos_of_neZero deg
  set r : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) with hr
  have hδ' : δ < 1 - r.sqrt := by
    simpa [ReedSolomon.sqrtRate, ← hr] using hδ
  have hJ' : (1 - r) / 2 < δ := by
    simpa [hr] using hJ
  have hnotUD : ¬δ ≤ (1 - r) / 2 := not_le_of_gt hJ'
  have hmem2 : (1 - r) / 2 < δ ∧ δ < 1 - r.sqrt := ⟨hJ', hδ'⟩
  simp only [errorBound, ← hr, Set.mem_Icc, zero_le, hnotUD, and_false,
    ↓reduceIte, Set.mem_Ioo, hmem2, and_self, coe_pow, NNReal.coe_natCast,
    coe_min, NNReal.coe_div, Real.coe_sqrt, NNReal.coe_ofNat, ge_iff_le]
  change (↑(Fintype.card ι + 1) / ↑(Fintype.card F) : ℝ) ≤
    (↑deg ^ 2 : ℝ) /
      ((2 * min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20)) ^ 7 *
        (Fintype.card F : ℝ))
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hqne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hqpos
  field_simp [hqne]
  set m : ℝ := min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20) with hm
  simp only [ge_iff_le]
  have hm_le : m ≤ Real.sqrt (r : ℝ) / 20 := by
    simp [hm]
  have hm_nonneg : 0 ≤ m := by
    have h1 : (0 : ℝ) ≤ (↑(1 - sqrt r - δ) : ℝ) := by
      exact_mod_cast (show (0 : ℝ≥0) ≤ (1 - sqrt r - δ) from zero_le _)
    have h2 : (0 : ℝ) ≤ Real.sqrt (r : ℝ) / 20 := by
      have : (0 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have : (0 : ℝ) ≤ min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20) :=
      le_min h1 h2
    simpa [hm] using this
  have hr_le_one : r ≤ 1 := by
    have h := DivergenceOfSets.reedSolomon_rate_le_one (deg := deg) (domain := domain)
    have : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) ≤ 1 := by
      exact_mod_cast h
    simpa [hr] using this
  have h_sqrt_le_one : Real.sqrt (r : ℝ) ≤ 1 := by
    have : (r : ℝ) ≤ (1 : ℝ) := by
      exact_mod_cast hr_le_one
    have := Real.sqrt_le_sqrt this
    simpa using this
  have h2m_le_one : 2 * m ≤ 1 := by
    have h2m_le_sqrt10 : 2 * m ≤ Real.sqrt (r : ℝ) / 10 := by
      have : 2 * m ≤ 2 * (Real.sqrt (r : ℝ) / 20) := by
        gcongr
      nlinarith
    have hsqrt10_le_one : Real.sqrt (r : ℝ) / 10 ≤ 1 := by
      have : Real.sqrt (r : ℝ) / 10 ≤ 1 / 10 := by
        nlinarith [h_sqrt_le_one]
      linarith
    exact h2m_le_sqrt10.trans hsqrt10_le_one
  have h2m_nonneg : 0 ≤ 2 * m := by nlinarith [hm_nonneg]
  have hpow7_le_pow2 : (2 * m) ^ 7 ≤ (2 * m) ^ 2 := by
    exact pow_le_pow_of_le_one h2m_nonneg h2m_le_one (by decide : (2 : ℕ) ≤ 7)
  have hpow2_le : (2 * m) ^ 2 ≤ (Real.sqrt (r : ℝ) / 10) ^ 2 := by
    have hle : 2 * m ≤ Real.sqrt (r : ℝ) / 10 := by
      have : 2 * m ≤ 2 * (Real.sqrt (r : ℝ) / 20) := by
        gcongr
      nlinarith
    have hsqrt10_nonneg : 0 ≤ Real.sqrt (r : ℝ) / 10 := by
      have : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have habs : |2 * m| ≤ |Real.sqrt (r : ℝ) / 10| := by
      have ha : 0 ≤ 2 * m := h2m_nonneg
      have hb : 0 ≤ Real.sqrt (r : ℝ) / 10 := hsqrt10_nonneg
      simpa [abs_of_nonneg ha, abs_of_nonneg hb] using hle
    have := (sq_le_sq).2 habs
    simpa using this
  have hsqrt_sq : (Real.sqrt (r : ℝ) / 10) ^ 2 = (r : ℝ) / 100 := by
    simpa using (DivergenceOfSets.real_sqrt_div_10_pow_two (r := r))
  have h2m_pow7_le : (2 * m) ^ 7 ≤ (r : ℝ) / 100 := by
    calc
      (2 * m) ^ 7 ≤ (2 * m) ^ 2 := hpow7_le_pow2
      _ ≤ (Real.sqrt (r : ℝ) / 10) ^ 2 := hpow2_le
      _ = (r : ℝ) / 100 := hsqrt_sq
  have hr_pos : (0 : ℝ) < (r : ℝ) := by
    have hrate_posQ : (0 : ℚ≥0) < LinearCode.rate (ReedSolomon.code domain deg) :=
      DivergenceOfSets.reedSolomon_rate_pos (deg := deg) (domain := domain) hdeg
    have hrate_pos :
        (0 : ℝ≥0) < (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) := by
      exact_mod_cast hrate_posQ
    have : (0 : ℝ≥0) < r := by
      simpa [hr] using hrate_pos
    exact_mod_cast this
  have hm_pos : 0 < m := by
    have hA_nnreal : (0 : ℝ≥0) < (1 - sqrt r - δ) := tsub_pos_of_lt hδ'
    have hA : (0 : ℝ) < (↑(1 - sqrt r - δ) : ℝ) := by exact_mod_cast hA_nnreal
    have hB : (0 : ℝ) < Real.sqrt (r : ℝ) / 20 := by
      have hsqrt_pos : (0 : ℝ) < Real.sqrt (r : ℝ) := (Real.sqrt_pos).2 hr_pos
      nlinarith
    have : 0 < min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20) :=
      lt_min hA hB
    simpa [hm] using this
  have hm7_pos : 0 < m ^ 7 := by
    simpa using (pow_pos hm_pos 7)
  have hmul_goal : (↑(Fintype.card ι + 1) * 2 ^ 7) * m ^ 7 ≤ (↑deg ^ 2 : ℝ) := by
    have h2pow_mul : (2 : ℝ) ^ 7 * m ^ 7 ≤ (r : ℝ) / 100 := by
      simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h2m_pow7_le
    have hcard_nonneg : 0 ≤ (↑(Fintype.card ι + 1) : ℝ) := by
      exact_mod_cast (Nat.zero_le (Fintype.card ι + 1))
    have hstep1 : (↑(Fintype.card ι + 1) : ℝ) * ((2 : ℝ) ^ 7 * m ^ 7) ≤
        (↑(Fintype.card ι + 1) : ℝ) * ((r : ℝ) / 100) := by
      exact mul_le_mul_of_nonneg_left h2pow_mul hcard_nonneg
    have hrmul_nnreal : (Fintype.card ι : ℝ≥0) * r ≤ (deg : ℝ≥0) := by
      simpa [hr] using
        (DivergenceOfSets.reedSolomon_rate_mul_card_le_deg (deg := deg) (domain := domain))
    have hrmul : (↑(Fintype.card ι) : ℝ) * (r : ℝ) ≤ (deg : ℝ) := by
      exact_mod_cast hrmul_nnreal
    have hr_le_one_real : (r : ℝ) ≤ 1 := by
      exact_mod_cast hr_le_one
    have hsucc_r : (↑(Fintype.card ι + 1) : ℝ) * (r : ℝ) ≤ (deg : ℝ) + 1 := by
      norm_num [Nat.cast_add]
      nlinarith
    have hsucc_div : (↑(Fintype.card ι + 1) : ℝ) * ((r : ℝ) / 100) ≤
        ((deg : ℝ) + 1) / 100 := by
      nlinarith [hsucc_r]
    have hdeg_sq : ((deg : ℝ) + 1) / 100 ≤ (↑deg ^ 2 : ℝ) := by
      have hdeg1_nat : 1 ≤ deg := Nat.one_le_of_lt hdeg
      have hdeg1 : (1 : ℝ) ≤ (deg : ℝ) := by
        exact_mod_cast hdeg1_nat
      nlinarith
    have hfinal : (↑(Fintype.card ι + 1) : ℝ) * ((2 : ℝ) ^ 7 * m ^ 7) ≤
        (↑deg ^ 2 : ℝ) :=
      hstep1.trans (hsucc_div.trans hdeg_sq)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hfinal
  have : (↑(Fintype.card ι + 1) * 2 ^ 7 : ℝ) ≤ (↑deg ^ 2 : ℝ) / m ^ 7 := by
    exact (le_div_iff₀ hm7_pos).2 (by
      simpa [mul_assoc] using hmul_goal)
  simpa [mul_assoc] using this

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
/-- In the Johnson-side branch, failure of the strict Johnson upper bound puts
`errorBound` in its fallback branch. This isolates the only boundary case not
covered by the strict list-decoding front door. -/
theorem errorBound_eq_zero_of_johnson_not_lt_sqrt {deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hnot : ¬δ < 1 - ReedSolomon.sqrtRate deg domain) :
    errorBound δ deg domain = 0 := by
  classical
  have hnotUD :
      ¬δ ≤ (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 :=
    not_le_of_gt hJ
  have hnotJ :
      ¬((1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ ∧
        δ < 1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt) := by
    intro h
    exact hnot (by simpa [ReedSolomon.sqrtRate] using h.2)
  simp [errorBound, Set.mem_Icc, Set.mem_Ioo, hnotUD, hnotJ]

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype F] in
/-- Under the capstone hypothesis `δ ≤ 1 - sqrtRate`, the non-strict Johnson
branch is exactly the closed square-root boundary. -/
theorem eq_sqrt_boundary_of_le_sqrt_and_not_lt {deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hnot : ¬δ < 1 - ReedSolomon.sqrtRate deg domain) :
    δ = 1 - ReedSolomon.sqrtRate deg domain :=
  le_antisymm hδ (not_lt.mp hnot)

omit [DecidableEq ι] in
/-- In the closed Johnson boundary, the curve-theorem probability hypothesis
only implies that there is at least one good coefficient. The stronger
cardinality lower bounds used by the list-decoding assembly are supplied only
in the strict Johnson branch. -/
theorem goodCoeffsCurve_card_pos_of_prob_gt_johnson_boundary
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hnot : ¬δ < 1 - ReedSolomon.sqrtRate deg domain) :
    0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card := by
  classical
  have hε0 : errorBound δ deg domain = 0 :=
    errorBound_eq_zero_of_johnson_not_lt_sqrt (deg := deg) (domain := domain) hJ hnot
  have hprob0 :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] > (0 : ENNReal) := by
    simpa [hε0] using hprob
  exact goodCoeffsCurve_card_pos_of_prob_gt_zero
    (deg := deg) (domain := domain) (δ := δ) u hprob0

omit [DecidableEq ι] in
/-- In the capstone's closed square-root boundary branch, the probability
hypothesis identifies the branch as equality at `1 - sqrtRate` and still gives a
nonempty good-coefficient set. -/
theorem goodCoeffsCurve_card_pos_of_prob_gt_closed_sqrt_boundary
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (u : WordStack F (Fin (k + 1)) ι)
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hnot : ¬δ < 1 - ReedSolomon.sqrtRate deg domain) :
    δ = 1 - ReedSolomon.sqrtRate deg domain ∧
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card := by
  exact ⟨eq_sqrt_boundary_of_le_sqrt_and_not_lt
      (deg := deg) (domain := domain) hδ hnot,
    goodCoeffsCurve_card_pos_of_prob_gt_johnson_boundary
      (deg := deg) (domain := domain) (δ := δ) u hprob hJ hnot⟩

omit [DecidableEq ι] in
/-- Strict Johnson-range front door with the standard `|ι| / |F|`
lower bound discharged from `errorBound_ge_const` and the stronger successor
threshold discharged from the Johnson expression for `errorBound`. The remaining
hypothesis is exactly the §5 coefficient-polynomial extraction witness. -/
theorem RS_jointAgreement_of_prob_gt_strict_johnson_and_coeff_polys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hcoeffPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds
    (deg := deg) (domain := domain) (δ := δ) hk u hprob
    (DivergenceOfSets.errorBound_ge_const (deg := deg) (domain := domain)
      (Nat.pos_of_neZero deg) hδ)
    (errorBound_ge_succ_const_of_strict_johnson (deg := deg) (domain := domain)
      hJ hδ)
    hcoeffPoly

omit [DecidableEq ι] [Fintype F] in
/-- The Johnson-list branch below the square-root rate bound can only occur in
the non-full Reed-Solomon regime. If `deg > |ι|`, the code rate is `1`, so the
rate-half lower bound forces `0 < δ` while the square-root upper bound forces
`δ ≤ 0`. -/
lemma RS_degree_le_domain_card_of_rate_half_lt_and_le_sqrt {deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0}
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    deg ≤ Fintype.card ι := by
  classical
  by_contra hdeg
  push Not at hdeg
  have hrate_eq : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) = 1 := by
    rw [ReedSolomon.rateOfLinearCode_eq_min_div]
    have hcard_ne : (Fintype.card ι : ℚ≥0) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := ι))
    have hmin : min deg (Fintype.card ι) = Fintype.card ι := by omega
    simp [hmin, hcard_ne]
  have hδpos : 0 < δ := by
    simpa [hrate_eq] using hJ
  have hδzero : δ ≤ 0 := by
    simpa [ReedSolomon.sqrtRate, hrate_eq] using hδ
  exact (not_lt_of_ge hδzero) hδpos

omit [DecidableEq ι] in
/-- Strict Johnson front door when §5 supplies pointwise evaluation-polynomial
dependence rather than coefficient-polynomial dependence. -/
theorem RS_jointAgreement_of_prob_gt_strict_johnson_and_eval_polys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hEvalPoly : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ E : ι → Polynomial F,
          (∀ x, (E x).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ x, (P z).eval (domain x) = (E x).eval z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds_eval_polys
    (deg := deg) (domain := domain) (δ := δ) hk
    (RS_degree_le_domain_card_of_rate_half_lt_and_le_sqrt
      (deg := deg) (domain := domain) hJ (le_of_lt hδ))
    u hprob
    (DivergenceOfSets.errorBound_ge_const (deg := deg) (domain := domain)
      (Nat.pos_of_neZero deg) hδ)
    (errorBound_ge_succ_const_of_strict_johnson (deg := deg) (domain := domain)
      hJ hδ)
    hEvalPoly

omit [DecidableEq ι] in
/-- Strict Johnson front door when §5 supplies one canonical decoded family,
an evaluation-polynomial witness for that family, and uniqueness of decoded
families on the good coefficient set. -/
theorem RS_jointAgreement_of_prob_gt_strict_johnson_and_canonical_eval_polys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (P₀ : F → Polynomial F)
    (hEval₀ : ∃ E : ι → Polynomial F,
      (∀ x, (E x).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ x, (P₀ z).eval (domain x) = (E x).eval z)
    (huniq : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          P z = P₀ z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact RS_jointAgreement_of_prob_gt_strict_johnson_and_eval_polys
    (deg := deg) (domain := domain) (δ := δ) hk u hprob hJ hδ
    (eval_polys_for_all_decoded_of_canonical_agreement
      (deg := deg) (domain := domain) (δ := δ)
      (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
      (u := u) P₀ hEval₀ huniq)

omit [DecidableEq ι] in
/-- Strict Johnson front door when §5 supplies one canonical decoded family,
coefficient-polynomial witnesses for that family, and uniqueness of decoded
families on the good coefficient set. -/
theorem RS_jointAgreement_of_prob_gt_strict_johnson_and_canonical_coeff_polys
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hk : 0 < k)
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob :
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)))
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (P₀ : F → Polynomial F)
    (hCoeff₀ : ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P₀ z).coeff j = (B j).eval z)
    (huniq : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          P z = P₀ z) :
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u) := by
  exact RS_jointAgreement_of_prob_gt_strict_johnson_and_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hk u hprob hJ hδ
    (coeff_polys_for_all_decoded_of_canonical_agreement
      (deg := deg) (domain := domain) (δ := δ)
      (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
      (u := u) P₀ hCoeff₀ huniq)

omit [DecidableEq ι] [Fintype F] in
/-- For Reed-Solomon codes, the rate-half radius is the relative unique-decoding
radius in the non-full-code case, and is `0` in the full-code case. This lets
the final curve theorem route the closed `errorBound` branch through the
unique-decoding proof even when it is phrased using the rate expression. -/
lemma RS_le_relativeUniqueDecodingRadius_of_le_rate_half {deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2) :
    δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg) := by
  classical
  by_cases hdeg : deg ≤ Fintype.card ι
  · have hrate_eq : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) =
        (deg : ℝ≥0) / (Fintype.card ι : ℝ≥0) := by
      have hdim := ReedSolomon.dim_eq_deg_of_le' (α := domain) (n := deg) hdeg
      simp [LinearCode.rate, hdim, LinearCode.length]
    rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq' (α := domain) (n := deg) hdeg]
    simpa [hrate_eq] using hδ
  · push Not at hdeg
    have hrate_eq : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) = 1 := by
      rw [ReedSolomon.rateOfLinearCode_eq_min_div]
      have hcard_ne : (Fintype.card ι : ℚ≥0) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero (α := ι))
      have hmin : min deg (Fintype.card ι) = Fintype.card ι := by omega
      simp [hmin, hcard_ne]
    have hδ0 : δ ≤ 0 := by
      simpa [hrate_eq] using hδ
    exact le_trans hδ0 (zero_le _)

omit [DecidableEq ι] in
/-- Final curve theorem with the two list-decoding obligations made explicit.

The unique-decoding regime and the closed rate-half branch are discharged in
this file. The remaining list-decoding work is exactly:
* the strict Johnson branch, where the §5 extraction supplies coefficient or
  evaluation polynomials; and
* the closed square-root boundary, where `errorBound = 0` and the probability
  hypothesis only gives nonempty `RS_goodCoeffsCurve`.
-/
theorem correlatedAgreement_affine_curves_of_list_decoding_obligations {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (_hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrict : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u))
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact RS_correlatedAgreement_curves_k_zero (deg := deg) (domain := domain) (δ := δ)
  · by_cases hUDR : δ ≤ Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
        (C := ReedSolomon.code domain deg)
    · exact RS_correlatedAgreement_curves_uniqueDecodingRegime hkpos hUDR
    · unfold δ_ε_correlatedAgreementCurves
      intro u hprob
      by_cases hJ :
          (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ
      · by_cases hsqrt : δ < 1 - ReedSolomon.sqrtRate deg domain
        · exact hStrict hkpos u hprob hJ hsqrt
        · exact hBoundary hkpos u hprob hJ hsqrt
      · push Not at hJ
        exact False.elim (hUDR
          (RS_le_relativeUniqueDecodingRadius_of_le_rate_half
            (deg := deg) (domain := domain) (δ := δ) hJ))

omit [DecidableEq ι] in
/-- Final curve theorem assuming the strict Johnson branch supplies the
pointwise evaluation-polynomial dependence produced by the §5 list-decoding
machinery. This discharges all threshold arithmetic and coefficient assembly in
the strict branch; the only remaining non-strict obligation is the closed
square-root boundary. -/
theorem correlatedAgreement_affine_curves_of_strict_eval_polys_and_boundary {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictEval : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ E : ι → Polynomial F,
            (∀ x, (E x).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ x, (P z).eval (domain x) = (E x).eval z)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_list_decoding_obligations
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  intro hk u hprob hJ hsqrt
  exact RS_jointAgreement_of_prob_gt_strict_johnson_and_eval_polys
    (deg := deg) (domain := domain) (δ := δ) hk u hprob hJ hsqrt
    (hStrictEval hk u hprob hJ hsqrt)

omit [DecidableEq ι] in
/-- Evaluation-polynomial capstone with canonical decoded-family data in the
strict Johnson branch and the original closed-boundary obligation left
explicit. -/
theorem correlatedAgreement_affine_curves_of_strict_canonical_eval_polys_and_boundary
    {k : ℕ} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalEval :
      ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate deg domain →
        ∃ P₀ : F → Polynomial F,
          (∃ E : ι → Polynomial F,
            (∀ x, (E x).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ x, (P₀ z).eval (domain x) = (E x).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_eval_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨P₀, hEval₀, huniq⟩ := hStrictCanonicalEval hk u hprob hJ hsqrt
  exact eval_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hEval₀ huniq P hP

omit [DecidableEq ι] in
/-- Evaluation-polynomial capstone with the closed square-root boundary
reduced to equality at the boundary and nonemptiness of the good-coefficient
set. -/
theorem correlatedAgreement_affine_curves_of_strict_eval_polys_and_boundary_card {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictEval : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ E : ι → Polynomial F,
            (∀ x, (E x).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ x, (P z).eval (domain x) = (E x).eval z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_eval_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictEval ?_
  intro hk u hprob hJ hnot
  obtain ⟨hδeq, hcard⟩ :=
    goodCoeffsCurve_card_pos_of_prob_gt_closed_sqrt_boundary
      (deg := deg) (domain := domain) (δ := δ) u hδ hprob hJ hnot
  exact hBoundaryCard hk u hδeq hcard

omit [DecidableEq ι] in
/-- Evaluation-polynomial capstone when the strict Johnson §5 branch supplies
one canonical decoded family, evaluation-polynomial witnesses for it, and
uniqueness of decoded families on the good-coefficient set. -/
theorem correlatedAgreement_affine_curves_of_strict_canonical_eval_polys_and_boundary_card
    {k : ℕ} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalEval :
      ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate deg domain →
        ∃ P₀ : F → Polynomial F,
          (∃ E : ι → Polynomial F,
            (∀ x, (E x).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ x, (P₀ z).eval (domain x) = (E x).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_eval_polys_and_boundary_card
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundaryCard
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨P₀, hEval₀, huniq⟩ := hStrictCanonicalEval hk u hprob hJ hsqrt
  exact eval_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hEval₀ huniq P hP

omit [DecidableEq ι] in
/-- Strict square-root-radius capstone. In the strict range
`δ < 1 - sqrtRate`, the closed-boundary branch is impossible, so the final
curve theorem follows from only the strict Johnson §5 evaluation-polynomial
extraction. -/
theorem correlatedAgreement_affine_curves_of_strict_eval_polys {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictEval : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ E : ι → Polynomial F,
            (∀ x, (E x).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ x, (P z).eval (domain x) = (E x).eval z) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_eval_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) (le_of_lt hδ) ?_ ?_
  · intro hk u hprob hJ _hsqrt P hP
    exact hStrictEval hk u hprob hJ P hP
  · intro _hk _u _hprob _hJ hnot
    exact False.elim (hnot hδ)

omit [DecidableEq ι] in
/-- Strict square-root-radius capstone when §5 supplies one canonical decoded
family, evaluation-polynomial witnesses for it, and uniqueness of decoded
families on the good-coefficient set. -/
theorem correlatedAgreement_affine_curves_of_strict_canonical_eval_polys {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalEval :
      ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        ∃ P₀ : F → Polynomial F,
          (∃ E : ι → Polynomial F,
            (∀ x, (E x).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ x, (P₀ z).eval (domain x) = (E x).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_eval_polys
    (deg := deg) (domain := domain) (δ := δ) hδ ?_
  intro hk u hprob hJ P hP
  obtain ⟨P₀, hEval₀, huniq⟩ := hStrictCanonicalEval hk u hprob hJ
  exact eval_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hEval₀ huniq P hP

omit [DecidableEq ι] in
/-- Final curve theorem assuming the strict Johnson branch supplies
coefficient-polynomial dependence, the native output shape of the §5
list-decoding chain. The non-strict square-root boundary remains explicit. -/
theorem correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCoeff : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_list_decoding_obligations
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  intro hk u hprob hJ hsqrt
  exact RS_jointAgreement_of_prob_gt_strict_johnson_and_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hk u hprob hJ hsqrt
    (hStrictCoeff hk u hprob hJ hsqrt)

omit [DecidableEq ι] in
/-- Coefficient-polynomial capstone with canonical decoded-family data in the
strict Johnson branch and the original closed-boundary obligation left
explicit. -/
theorem correlatedAgreement_affine_curves_of_strict_canonical_coeff_polys_and_boundary
    {k : ℕ} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff :
      ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate deg domain →
        ∃ P₀ : F → Polynomial F,
          (∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨P₀, hCoeff₀, huniq⟩ := hStrictCanonicalCoeff hk u hprob hJ hsqrt
  exact coeff_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hCoeff₀ huniq P hP

omit [DecidableEq ι] in
/-- Coefficient-polynomial capstone with the closed square-root boundary
reduced to its actual data: equality at the boundary and a nonempty
good-coefficient set. -/
theorem correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary_card {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCoeff : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictCoeff ?_
  intro hk u hprob hJ hnot
  obtain ⟨hδeq, hcard⟩ :=
    goodCoeffsCurve_card_pos_of_prob_gt_closed_sqrt_boundary
      (deg := deg) (domain := domain) (δ := δ) u hδ hprob hJ hnot
  exact hBoundaryCard hk u hδeq hcard

omit [DecidableEq ι] in
/-- Coefficient-polynomial capstone when the strict Johnson §5 branch supplies
one canonical decoded family, coefficient-polynomial witnesses for it, and
uniqueness of decoded families on the good-coefficient set. -/
theorem correlatedAgreement_affine_curves_of_strict_canonical_coeff_polys_and_boundary_card
    {k : ℕ} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff :
      ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate deg domain →
        ∃ P₀ : F → Polynomial F,
          (∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary_card
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundaryCard
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨P₀, hCoeff₀, huniq⟩ := hStrictCanonicalCoeff hk u hprob hJ hsqrt
  exact coeff_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hCoeff₀ huniq P hP

omit [DecidableEq ι] in
/-- Coefficient-polynomial capstone with uniform strict-branch extraction and
the closed square-root boundary reduced to equality plus nonemptiness of the
good-coefficient set. This is the closed-radius counterpart of
`correlatedAgreement_affine_curves_of_uniform_strict_coeff_polys`. -/
theorem correlatedAgreement_affine_curves_of_uniform_strict_coeff_polys_and_boundary_card
    {k : ℕ} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hCoeff : ∀ u : WordStack F (Fin (k + 1)) ι,
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary_card
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundaryCard
  intro _hk u _hprob _hJ _hsqrt P hP
  exact hCoeff u P hP

omit [DecidableEq ι] in
/-- Closed-radius coefficient-polynomial capstone when the strict branch
supplies one canonical decoded family uniformly in the received word stack.
This is the canonical-family version of
`correlatedAgreement_affine_curves_of_uniform_strict_coeff_polys_and_boundary_card`. -/
theorem correlatedAgreement_affine_curves_of_uniform_strict_canonical_coeff_polys_and_boundary_card
    {k : ℕ} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff :
      ∀ u : WordStack F (Fin (k + 1)) ι,
        ∃ P₀ : F → Polynomial F,
          (∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_uniform_strict_coeff_polys_and_boundary_card
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundaryCard
  intro u P hP
  obtain ⟨P₀, hCoeff₀, huniq⟩ := hStrictCanonicalCoeff u
  exact coeff_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hCoeff₀ huniq P hP

omit [DecidableEq ι] in
/-- Strict square-root-radius capstone phrased in the coefficient-polynomial
language of §5. In the strict range, the closed-boundary branch is impossible. -/
theorem correlatedAgreement_affine_curves_of_strict_coeff_polys {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCoeff : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) (le_of_lt hδ) ?_ ?_
  · intro hk u hprob hJ _hsqrt P hP
    exact hStrictCoeff hk u hprob hJ P hP
  · intro _hk _u _hprob _hJ hnot
    exact False.elim (hnot hδ)

omit [DecidableEq ι] in
/-- Strict square-root-radius coefficient-polynomial capstone when the §5
coefficient-polynomial extraction is uniform in the received word stack. This is
the natural shape of selected-domain extraction: the probability and Johnson
side conditions are only needed by the §6 threshold front door, not by the
coefficient assembly witness itself. -/
theorem correlatedAgreement_affine_curves_of_uniform_strict_coeff_polys {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hCoeff : ∀ u : WordStack F (Fin (k + 1)) ι,
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hδ ?_
  intro _hk u _hprob _hJ P hP
  exact hCoeff u P hP

omit [DecidableEq ι] in
/-- Strict square-root-radius coefficient-polynomial capstone when the strict
branch supplies one canonical decoded family uniformly in the received word
stack. This is the strict-radius counterpart of
`correlatedAgreement_affine_curves_of_uniform_strict_canonical_coeff_polys_and_boundary_card`. -/
theorem correlatedAgreement_affine_curves_of_uniform_strict_canonical_coeff_polys {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff :
      ∀ u : WordStack F (Fin (k + 1)) ι,
        ∃ P₀ : F → Polynomial F,
          (∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_uniform_strict_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hδ ?_
  intro u P hP
  obtain ⟨P₀, hCoeff₀, huniq⟩ := hStrictCanonicalCoeff u
  exact coeff_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hCoeff₀ huniq P hP

omit [DecidableEq ι] in
/-- Strict square-root-radius coefficient-polynomial capstone when §5 supplies
one canonical decoded family, coefficient-polynomial witnesses for it, and
uniqueness of decoded families on the good-coefficient set. -/
theorem correlatedAgreement_affine_curves_of_strict_canonical_coeff_polys {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff :
      ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        ∃ P₀ : F → Polynomial F,
          (∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hδ ?_
  intro hk u hprob hJ P hP
  obtain ⟨P₀, hCoeff₀, huniq⟩ := hStrictCanonicalCoeff hk u hprob hJ
  exact coeff_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hCoeff₀ huniq P hP

omit [DecidableEq ι] in
/-- Explicit residual for the strict Johnson list-decoding extraction needed by the final
correlated-agreement keystone. -/
def StrictCoeffPolysResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z

omit [DecidableEq ι] in
/-- Canonical-family form of the strict Johnson extraction residual. This is
strictly more structured than `StrictCoeffPolysResidual`: the §5 side supplies
one decoded family, coefficient-polynomial witnesses for that family, and
uniqueness for every other decoded family on the same good-coefficient set. -/
def StrictCanonicalCoeffPolysResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∃ P₀ : F → Polynomial F,
      (∃ B : ℕ → Polynomial F,
        (∀ j < deg, (B j).natDegree < k + 1) ∧
          ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          P z = P₀ z

omit [DecidableEq ι] in
/-- The canonical-family extraction residual discharges the raw
coefficient-polynomial residual by transporting the canonical coefficient
witnesses across uniqueness of decoded families. -/
theorem strictCoeffPolysResidual_of_strictCanonicalCoeffPolysResidual
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hCanonical :
      StrictCanonicalCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨P₀, hCoeff₀, huniq⟩ := hCanonical hk u hprob hJ hsqrt
  exact coeff_polys_for_all_decoded_of_canonical_agreement
    (deg := deg) (domain := domain) (δ := δ)
    (S := RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (u := u) P₀ hCoeff₀ huniq P hP

/-- Explicit residual for the closed square-root boundary assembly needed by the final
correlated-agreement keystone.

**REFUTED — this Prop is FALSE as stated** (axiom-clean, in-tree):
`BoundaryCardResidualRefutation.not_boundaryCardResidual`
(`BoundaryCardResidualRefutation.lean`), with further counterexample families in
`not_boundaryCardResidual_affineLine` (`BoundaryCardResidualAffineLineRefutation.lean`) and
`not_boundaryCardResidual_nonSquareEndpoint` (`BoundaryCardStrictInteriorRefutation.lean`).
Even the formalized Thm-1.5 conclusion fails at the closed boundary
(`not_delta_epsilon_correlatedAgreementCurves_boundary`).  This def is retained ONLY as a
documented-false assumption surface for explicitly-conditional adapters
(e.g. `correlatedAgreement_affine_curves_of_boundaryCardResidual`); do not try to discharge it. -/
def BoundaryCardResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    δ = 1 - ReedSolomon.sqrtRate deg domain →
    0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)

omit [DecidableEq ι] in
/-- Exact residual needed by the non-strict boundary branch of the list-decoding
assembly. Unlike `BoundaryCardResidual`, this retains the probability and
Johnson-side hypotheses available at the branch point, so callers do not have
to prove `jointAgreement` for every merely nonempty good-coefficient set in
strict branches. At the exact square-root endpoint, however, `errorBound = 0`,
so this is still only an explicit assumption surface rather than an automatic
boundary theorem.

**REFUTED — this Prop is FALSE as stated** (axiom-clean, in-tree):
`BoundaryCardResidualRefutation.not_boundaryProbabilityResidual`
(`BoundaryCardResidualRefutation.lean`).  Retained ONLY as a documented-false assumption
surface for explicitly-conditional adapters; do not try to discharge it. -/
def BoundaryProbabilityResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
    jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)

omit [DecidableEq ι] in
/-- The older closed-boundary cardinality residual implies the sharper
probability-branch residual by extracting boundary equality and nonemptiness
from the branch hypotheses. -/
theorem boundaryProbabilityResidual_of_boundaryCardResidual
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hBoundaryCard :
      BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hnot
  obtain ⟨hδeq, hcard⟩ :=
    goodCoeffsCurve_card_pos_of_prob_gt_closed_sqrt_boundary
      (deg := deg) (domain := domain) (δ := δ) u hδ hprob hJ hnot
  exact hBoundaryCard hk u hδeq hcard

/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

This theorem is fully proved from two explicit list-decoding residuals:
`StrictCoeffPolysResidual` for the strict Johnson branch and
`BoundaryProbabilityResidual` for the closed square-root boundary branch. The
older `BoundaryCardResidual` still implies this boundary residual via
`boundaryProbabilityResidual_of_boundaryCardResidual`. -/
theorem correlatedAgreement_affine_curves {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    -- `deg = 0` makes the statement false: `errorBound`'s Johnson
    -- branch vacates the threshold at deg = 0; counterexample in upstream-issues.md).
    [NeZero deg]
    (hStrictCoeff : StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hBoundary : BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  exact correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictCoeff hBoundary

/-- Compatibility wrapper for callers that still carry the older
closed-boundary cardinality residual. -/
theorem correlatedAgreement_affine_curves_of_boundaryCardResidual {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hStrictCoeff : StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact correlatedAgreement_affine_curves
    (deg := deg) (domain := domain) (δ := δ) hStrictCoeff
    (boundaryProbabilityResidual_of_boundaryCardResidual
      (deg := deg) (domain := domain) (δ := δ) hδ hBoundaryCard)
    hδ

/-- Canonical strict-branch compatibility wrapper for the sharpened final
residual surface. -/
theorem correlatedAgreement_affine_curves_of_strictCanonicalCoeffPolysResidual {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hStrictCanonical :
      StrictCanonicalCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hBoundary : BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  exact correlatedAgreement_affine_curves
    (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_strictCanonicalCoeffPolysResidual
      (deg := deg) (domain := domain) (δ := δ) hStrictCanonical)
    hBoundary hδ

/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves_legacy_statement {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    -- `deg = 0` makes the statement false: `errorBound`'s Johnson
    -- branch vacates the threshold at deg = 0; counterexample in upstream-issues.md).
      [NeZero deg]
      (hStrictCoeff : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate deg domain →
        ∀ P : F → Polynomial F,
          (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            (P z).natDegree < deg ∧
              δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                (P z).eval ∘ domain) ≤ δ) →
            ∃ B : ℕ → Polynomial F,
              (∀ j < deg, (B j).natDegree < k + 1) ∧
                ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                  ∀ j < deg, (P z).coeff j = (B j).eval z)
      (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        δ = 1 - ReedSolomon.sqrtRate deg domain →
        0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
        jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u))
      (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
      δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
        (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  exact correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary_card
      (deg := deg) (domain := domain) (δ := δ) hδ hStrictCoeff hBoundaryCard

end CoreResults

section BCIKS20ProximityGapSection6

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [Fintype F] [NeZero n] in
/-- The generic degree-one curve sum for `Code.finMapTwoWords` is the affine
line word. -/
lemma sum_finMapTwoWords_eq (u₀ u₁ : Fin n → F) (z : F) :
    (∑ t : Fin 2, (z ^ (t : ℕ)) • Code.finMapTwoWords u₀ u₁ t)
      = u₀ + z • u₁ := by
  funext x
  rw [Fin.sum_univ_two]
  change (z ^ (0 : ℕ)) * u₀ x + (z ^ (1 : ℕ)) * u₁ x = u₀ x + z * u₁ x
  ring

/-- The parameters for which the curve points are `δ`-close to a set `V`
(typically, a linear code). This is the set `S` from the proximity gap paper. -/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
    (δ : ℚ≥0) (u : Fin l → Fin n → F) (V : Set (Fin n → F)) : Finset F :=
  Finset.filter (fun z : F => δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ)
    Finset.univ

omit [NeZero n] in
/-- The §6 close-parameter set specialized to a Reed-Solomon code is the same
good-coefficient set used by the curve assembly layer. -/
theorem coeffs_of_close_proximity_curve_RS_toFinset_eq_goodCoeffsCurve
    {k deg : ℕ} {domain : Fin n ↪ F}
    (δ : ℚ≥0) (u : WordStack F (Fin (k + 1)) (Fin n)) :
    coeffs_of_close_proximity_curve (F := F) (n := n) (l := k + 1)
        δ u (ReedSolomon.toFinset domain deg) =
      RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u (δ : ℝ≥0) := by
  classical
  simp [coeffs_of_close_proximity_curve, RS_goodCoeffsCurve,
    ReedSolomon.toFinset, ReedSolomon.RScodeSet, polynomialCurveEval_eq_sum_smul,
    ENNReal.coe_nnratCast]

omit [NeZero n] in
/-- Membership form of
`coeffs_of_close_proximity_curve_RS_toFinset_eq_goodCoeffsCurve`. -/
theorem coeffs_of_close_proximity_curve_RS_toFinset_mem_iff_goodCoeffsCurve
    {k deg : ℕ} {domain : Fin n ↪ F}
    (δ : ℚ≥0) (u : WordStack F (Fin (k + 1)) (Fin n)) (z : F) :
    z ∈ coeffs_of_close_proximity_curve (F := F) (n := n) (l := k + 1)
        δ u (ReedSolomon.toFinset domain deg) ↔
      z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u (δ : ℝ≥0) := by
  rw [coeffs_of_close_proximity_curve_RS_toFinset_eq_goodCoeffsCurve
    (F := F) (n := n) (k := k) (deg := deg) (domain := domain) δ u]

omit [NeZero n] in
/-- Cardinality form of
`coeffs_of_close_proximity_curve_RS_toFinset_eq_goodCoeffsCurve`. -/
theorem coeffs_of_close_proximity_curve_RS_toFinset_card_eq_goodCoeffsCurve
    {k deg : ℕ} {domain : Fin n ↪ F}
    (δ : ℚ≥0) (u : WordStack F (Fin (k + 1)) (Fin n)) :
    (coeffs_of_close_proximity_curve (F := F) (n := n) (l := k + 1)
        δ u (ReedSolomon.toFinset domain deg)).card =
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u (δ : ℝ≥0)).card := by
  rw [coeffs_of_close_proximity_curve_RS_toFinset_eq_goodCoeffsCurve
    (F := F) (n := n) (k := k) (deg := deg) (domain := domain) δ u]

omit [NeZero n] in
/-- Strict cardinal lower bounds transport from the §6 close-parameter set to
the `RS_goodCoeffsCurve` set used by the curve assembly layer. -/
theorem coeffs_of_close_proximity_curve_RS_toFinset_card_gt_iff_goodCoeffsCurve
    {k deg : ℕ} {domain : Fin n ↪ F}
    (δ : ℚ≥0) (u : WordStack F (Fin (k + 1)) (Fin n)) (m : ℕ) :
    (coeffs_of_close_proximity_curve (F := F) (n := n) (l := k + 1)
        δ u (ReedSolomon.toFinset domain deg)).card > m ↔
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u
        (δ : ℝ≥0)).card > m := by
  rw [coeffs_of_close_proximity_curve_RS_toFinset_card_eq_goodCoeffsCurve
    (F := F) (n := n) (k := k) (deg := deg) (domain := domain) δ u]

omit [NeZero n] in
/-- Non-strict cardinal lower bounds transport from the §6 close-parameter set
to the `RS_goodCoeffsCurve` set used by the curve assembly layer. -/
theorem coeffs_of_close_proximity_curve_RS_toFinset_card_ge_iff_goodCoeffsCurve
    {k deg : ℕ} {domain : Fin n ↪ F}
    (δ : ℚ≥0) (u : WordStack F (Fin (k + 1)) (Fin n)) (m : ℕ) :
    (coeffs_of_close_proximity_curve (F := F) (n := n) (l := k + 1)
        δ u (ReedSolomon.toFinset domain deg)).card ≥ m ↔
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u
        (δ : ℝ≥0)).card ≥ m := by
  rw [coeffs_of_close_proximity_curve_RS_toFinset_card_eq_goodCoeffsCurve
    (F := F) (n := n) (k := k) (deg := deg) (domain := domain) δ u]

omit [DecidableEq F] in
/-- Propagation brick for the §6.1 argument: two polynomial curves of degree `< l`
that agree in coordinate `x` on at least `l` parameter values agree in that
coordinate everywhere. -/
private lemma polynomialCurveEval_coord_eq_of_agree {n l : ℕ} {F : Type} [Field F]
    {u v : Fin l → Fin n → F} {x : Fin n}
    {Zs : Finset F} (hZ : l ≤ Zs.card)
    (h : ∀ z ∈ Zs, Curve.polynomialCurveEval (F := F) (A := F) u z x
      = Curve.polynomialCurveEval (F := F) (A := F) v z x) :
    ∀ z : F, Curve.polynomialCurveEval (F := F) (A := F) u z x
      = Curve.polynomialCurveEval (F := F) (A := F) v z x := by
  -- coordinate-wise polynomial packaging
  have hEval : ∀ (a : Fin l → Fin n → F) (w : F),
      (∑ i : Fin l, Polynomial.C (a i x) * Polynomial.X ^ (i : ℕ)).eval w
        = Curve.polynomialCurveEval (F := F) (A := F) a w x := by
    intro a w
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdeg : ∀ (a : Fin l → Fin n → F),
      (∑ i : Fin l, Polynomial.C (a i x) * Polynomial.X ^ (i : ℕ)).degree < ((l : ℕ) : WithBot ℕ)
        := by
    intro a
    apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe l)]
    intro i _
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)
  have hPQ := Polynomial.eq_of_eval_eq_degree (n := l) (hdeg u) (hdeg v) Zs hZ
    (fun w hw => by rw [hEval u, hEval v]; exact h w hw)
  intro z
  calc Curve.polynomialCurveEval (F := F) (A := F) u z x
      = (∑ i : Fin l, Polynomial.C (u i x) * Polynomial.X ^ (i : ℕ)).eval z := (hEval u z).symm
    _ = (∑ i : Fin l, Polynomial.C (v i x) * Polynomial.X ^ (i : ℕ)).eval z := by rw [hPQ]
    _ = Curve.polynomialCurveEval (F := F) (A := F) v z x := hEval v z

/-- Counting brick for the §6.1 argument (generic double counting): if every
`z ∈ S` has a bad-set of size at most `m`, then the number of coordinates that
are bad for at least `t` elements of `S` is bounded: `t · #poor ≤ m · #S`. -/
private lemma card_heavyCoords_mul_le {α β : Type} [Fintype α] [DecidableEq α]
    {S : Finset β} {B : β → Finset α} {m : ℕ}
    (hB : ∀ z ∈ S, (B z).card ≤ m) (t : ℕ) :
    ((Finset.univ : Finset α).filter
      (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
      ≤ m * S.card := by
  classical
  -- double counting: Σ_x #{z ∈ S : x ∈ B z} = Σ_{z ∈ S} #(B z)
  have hswap : ∑ x : α, (S.filter (fun z => x ∈ B z)).card
      = ∑ z ∈ S, (B z).card := by
    have h1 : ∀ x : α, (S.filter (fun z => x ∈ B z)).card
        = ∑ z ∈ S, if x ∈ B z then 1 else 0 := fun x => Finset.card_filter _ _
    have h2 : ∀ z : β, (B z).card = ∑ x : α, if x ∈ B z then 1 else 0 := by
      intro z
      rw [← Finset.card_filter, Finset.filter_univ_mem]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hbound : ∑ z ∈ S, (B z).card ≤ m * S.card := by
    calc ∑ z ∈ S, (B z).card ≤ ∑ _z ∈ S, m := Finset.sum_le_sum hB
      _ = m * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hfilter : ((Finset.univ : Finset α).filter
      (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
      ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card := by
    calc ((Finset.univ : Finset α).filter
        (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card)).card * t
        = ∑ _x ∈ (Finset.univ : Finset α).filter
            (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card), t := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ (Finset.univ : Finset α).filter
            (fun x => t ≤ (S.filter (fun z => x ∈ B z)).card),
            (S.filter (fun z => x ∈ B z)).card :=
          Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x : α, (S.filter (fun z => x ∈ B z)).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  exact le_trans hfilter (hswap ▸ hbound)

omit [DecidableEq F] in
/-- Interpolation brick for the §6.1 argument: through any `l` distinct parameter
values and arbitrary target vectors there is a polynomial curve of degree `< l`. -/
private lemma exists_polynomialCurve_through {n l : ℕ} {F : Type} [Field F]
    (zs : Fin l → F) (hinj : Function.Injective zs)
    (w : Fin l → Fin n → F) :
    ∃ v : Fin l → Fin n → F,
      ∀ j, Curve.polynomialCurveEval (F := F) (A := F) v (zs j) = w j := by
  -- per-coordinate Lagrange interpolant
  classical
  set P : Fin n → Polynomial F :=
    fun x => Lagrange.interpolate Finset.univ zs (fun j => w j x) with hP
  have hdeg : ∀ x, (P x).degree < (l : WithBot ℕ) := by
    intro x
    simpa using Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin l)))
      (v := zs) (r := fun j => w j x) (fun a _ b _ hab => hinj hab)
  refine ⟨fun i x => (P x).coeff i, ?_⟩
  intro j
  funext x
  have hnat : (P x).natDegree < l := by
    rcases eq_or_ne (P x) 0 with h0 | h0
    · simpa [h0] using j.pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hdeg x)
  have heval : (P x).eval (zs j) = w j x :=
    Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (Fin l)))
      (v := zs) (r := fun j => w j x) (fun a _ b _ hab => hinj hab) (Finset.mem_univ j)
  calc Curve.polynomialCurveEval (F := F) (A := F) (fun i x => (P x).coeff i) (zs j) x
      = ∑ i : Fin l, (zs j) ^ (i : ℕ) * (P x).coeff i := by
        simp [Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ i ∈ Finset.range l, (P x).coeff i * (zs j) ^ i := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => (P x).coeff i * (zs j) ^ i)]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = (P x).eval (zs j) := (Polynomial.eval_eq_sum_range' hnat _).symm
    _ = w j x := heval

/-- Unique decoding brick for the §6.1 argument: two codewords of a code with
minimum distance `d` that are both within distance summing below `d` of a common
word are equal (triangle inequality). -/
private lemma eq_of_both_close_lt_minDist {n : ℕ} {F : Type} [DecidableEq F]
    {V : Finset (Fin n → F)} {d : ℕ}
    (hV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → d ≤ Δ₀(w, w'))
    {w₁ w₂ f : Fin n → F} (h₁ : w₁ ∈ V) (h₂ : w₂ ∈ V)
    (hsum : Δ₀(w₁, f) + Δ₀(f, w₂) < d) :
    w₁ = w₂ := by
  by_contra hne
  have htri : Δ₀(w₁, w₂) ≤ Δ₀(w₁, f) + Δ₀(f, w₂) := hammingDist_triangle w₁ f w₂
  exact absurd (le_trans (hV w₁ h₁ w₂ h₂ hne) htri) (not_le.mpr hsum)

/-- The distance bound from [BCIKS20]. -/
noncomputable def δ₀ (rho : ℚ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

/-- Engine branch of Theorem 6.1 (unique-decoding regime, `deg ≠ 0`): the joint-agreement
obligation for the degree-`k` curve through `u`, discharged through the proven Berlekamp-Welch
machinery `RS_jointAgreement_of_goodCoeffsCurve_card_gt`. The `deg = 0` corner (trivial code)
is handled separately since the engine requires `[NeZero deg]`. -/
private lemma large_agreement_set_on_curve_jointAgreement_of_neZero {k : ℕ}
    {deg : ℕ} [NeZero deg]
    {domain : Fin n ↪ F}
    {δ : ℚ≥0}
    (hδ : δ ≤ (1 - ρ (ReedSolomon.code domain deg)) / 2)
    (u : Fin (k + 1) → Fin n → F)
    (hS : (k + 1 - 1) * n <
      (coeffs_of_close_proximity_curve (F := F) δ u (ReedSolomon.code domain deg)).card) :
    jointAgreement (C := (ReedSolomon.code domain deg : Set (Fin n → F)))
      (δ := (δ : ℝ≥0)) (W := u) := by
  classical
  set δR : ℝ≥0 := (δ : ℝ≥0) with hδR
  -- Bridge the hypothesis `δ ≤ (1-ρ)/2` to the engine's UDR requirement.
  have hδUDR : δR ≤ Code.relativeUniqueDecodingRadius (ι := Fin n) (F := F)
      (C := ReedSolomon.code domain deg) := by
    rw [hδR]
    -- Cast the rate-half hypothesis from `ℚ≥0` to `ℝ≥0`, working through `ℝ` where the
    -- subtraction is genuine.
    set r : ℚ≥0 := LinearCode.rate (ReedSolomon.code domain deg) with hr
    have hcast : (δ : ℝ≥0) ≤ (1 - (r : ℝ≥0)) / 2 := by
      by_cases hle : r ≤ 1
      · have hrle : (r : ℝ≥0) ≤ 1 := by exact_mod_cast hle
        have hrleR : (r : ℝ) ≤ 1 := by exact_mod_cast hle
        -- All casts ℚ≥0 → ℝ normalize to a single `NNRat.cast` in ℝ, unifying the tsub.
        have hstep : ((δ : ℝ≥0) : ℝ) ≤ (((1 - (r : ℝ≥0)) / 2 : ℝ≥0) : ℝ) := by
          rw [NNReal.coe_div, NNReal.coe_sub hrle, NNReal.coe_one]
          have hqR : ((δ : ℝ)) ≤ (1 - (r : ℝ)) / 2 := by
            have hqQ : ((δ : ℚ≥0) : ℚ) ≤ (((1 - r) / 2 : ℚ≥0) : ℚ) := by exact_mod_cast hδ
            rw [NNRat.coe_div, NNRat.coe_sub hle, NNRat.coe_one] at hqQ
            have : ((δ : ℝ)) ≤ ((1 - (r : ℝ)) / 2 : ℝ) := by
              have h1 : ((((δ : ℚ≥0)) : ℚ) : ℝ) = ((δ : ℝ)) := by push_cast; ring
              have h2 : ((((1 - (r : ℚ)) / 2 : ℚ) : ℝ)) = (1 - (r : ℝ)) / 2 := by
                push_cast; ring
              calc ((δ : ℝ)) = ((((δ : ℚ≥0)) : ℚ) : ℝ) := by push_cast; ring
                _ ≤ ((((1 - (r : ℚ)) / 2 : ℚ) : ℝ)) := by exact_mod_cast hqQ
                _ = (1 - (r : ℝ)) / 2 := h2
            exact this
          -- Bridge `(δ:ℚ≥0:ℝ) = (δ:ℝ≥0:ℝ)` and `(r:ℚ≥0:ℝ) = (r:ℝ≥0:ℝ)`.
          have hbridge_delta : ((δ : ℝ)) = ((δ : ℝ≥0) : ℝ) := by norm_cast
          have hbridge_r : ((r : ℝ)) = ((r : ℝ≥0) : ℝ) := by norm_cast
          rw [hbridge_delta, hbridge_r] at hqR
          exact hqR
        exact_mod_cast hstep
      · push_neg at hle
        have h2 : (1 - (r : ℝ≥0)) = 0 := tsub_eq_zero_of_le (by exact_mod_cast hle.le)
        rw [h2, zero_div]
        have h1 : (1 - r : ℚ≥0) = 0 := tsub_eq_zero_of_le hle.le
        have : δ ≤ 0 := by simpa [h1] using hδ
        exact_mod_cast this
    exact RS_le_relativeUniqueDecodingRadius_of_le_rate_half (δ := (δ : ℝ≥0))
      (by rw [← hr]; exact hcast)
  -- Transport the cardinality bound to the `RS_goodCoeffsCurve` set.
  have hScoeff : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u
      (δ : ℝ≥0)).card > k * Fintype.card (Fin n) := by
    have hcoeffeq : coeffs_of_close_proximity_curve (F := F) (n := n) (l := k + 1)
        δ u (ReedSolomon.code domain deg)
          = coeffs_of_close_proximity_curve (F := F) (n := n) (l := k + 1)
            δ u (ReedSolomon.toFinset domain deg) := by
      simp only [coeffs_of_close_proximity_curve, ReedSolomon.toFinset, Set.coe_toFinset]
    have hgt : (coeffs_of_close_proximity_curve (F := F) (n := n) (l := k + 1)
        δ u (ReedSolomon.toFinset domain deg)).card > k * Fintype.card (Fin n) := by
      rw [← hcoeffeq]
      have hn : Fintype.card (Fin n) = n := by simp
      rw [hn]
      simpa [Nat.add_sub_cancel] using hS
    exact (coeffs_of_close_proximity_curve_RS_toFinset_card_gt_iff_goodCoeffsCurve
      (F := F) (n := n) (k := k) (deg := deg) (domain := domain) δ u
      (k * Fintype.card (Fin n))).1 hgt
  -- Split on `k`: the engine needs `0 < k`; `k = 0` (single word) is a direct unique-decode.
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the curve is the constant word `u 0`; the nonempty good set forces `u 0`
    -- to be `δ`-close to the code, and joint agreement follows by unique decoding.
    subst hk0
    have hne : (RS_goodCoeffsCurve (k := 0) (deg := deg) (domain := domain) u
        (δ : ℝ≥0)).Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℕ) * Fintype.card (Fin n) < (RS_goodCoeffsCurve (k := 0) (deg := deg)
        (domain := domain) u (δ : ℝ≥0)).card := hScoeff
      simpa using this
    obtain ⟨z, hz⟩ := hne
    have hclose : δᵣ(u 0, (ReedSolomon.code domain deg : Set (Fin n → F))) ≤ (δ : ℝ≥0) := by
      have hz' := hz
      simp only [RS_goodCoeffsCurve, Finset.mem_filter] at hz'
      by_contra hp
      exact hp (by simpa using hz'.2)
    set e : ℕ := Nat.floor ((δ : ℝ≥0) * Fintype.card (Fin n)) with he
    have hdist : Δ₀(u 0, (ReedSolomon.code domain deg : Set (Fin n → F))) ≤ (e : ℕ∞) := by
      have h := (Code.relDistFromCode_le_iff_distFromCode_le
          (u := u 0) (C := (ReedSolomon.code domain deg : Set (Fin n → F))) (δ := (δ : ℝ≥0))).1
        hclose
      simpa [e] using h
    rcases (Code.closeToCode_iff_closeToCodeword_of_minDist
          (u := u 0) (C := (ReedSolomon.code domain deg : Set (Fin n → F))) (e := e)).1 hdist with
      ⟨w, hwC, hwdist⟩
    obtain ⟨T, hT_card, hT_agree⟩ :=
      (Code.closeToWord_iff_exists_agreementCols (u := u 0) (v := w) (e := e)).1 hwdist
    refine ⟨T, ?_, fun _ => w, ?_⟩
    · have hnat : Fintype.card (Fin n) - e ≤ T.card := hT_card
      simpa [e, hδR] using
        (Code.relDist_floor_bound_iff_complement_bound (Fintype.card (Fin n)) T.card
          (δ : ℝ≥0)).mp (by simpa [e] using hnat)
    · intro t
      refine ⟨hwC, ?_⟩
      intro j hj
      have := (hT_agree j).1 hj
      have ht0 : t = 0 := Fin.fin_one_eq_zero t
      subst ht0; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact this.symm
  · -- `k ≥ 1`: invoke the Berlekamp-Welch engine.
    have hja := RS_jointAgreement_of_goodCoeffsCurve_card_gt (ι := Fin n) (F := F)
      (k := k) (deg := deg) (domain := domain) (δ := δR) hkpos hδUDR u
      (by simpa [hδR] using hScoeff)
    simpa [hδR] using hja

/-- Unique-decoding regime (`δ ≤ (1 - ρ) / 2`); companion of
`large_agreement_set_on_curve_implies_correlated_agreement'` (Johnson regime). This is
Theorem 6.1 of [BCIKS20]. `V` must be an actual Reed-Solomon code (of rate `ρ`, tied to `V` via
its degree/domain) rather than an arbitrary set of words: the conclusion is false for a `V` with
no algebraic structure connecting its elements, e.g. a `V` that is merely a "coincidentally
close" `Finset` unrelated to `ρ`. If more than `(l - 1) * n` points on the curve defined by `u`
are `δ`-close to `V`, then: every point of the curve is `δ`-close to `V`; there exist vectors `v`
from `V` such that every point of the `v`-curve is `δ`-close to the corresponding point of the
`u`-curve; and `u`, `v` agree outside a `δ`-fraction of coordinates. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement {l : ℕ}
    {deg : ℕ}
    {domain : Fin n ↪ F}
    {δ : ℚ≥0}
    (hδ : δ ≤ (1 - ρ (ReedSolomon.code domain deg)) / 2)
    {u : Fin l → Fin n → F}
    (hS : (l - 1) * n <
      (coeffs_of_close_proximity_curve (F := F) δ u (ReedSolomon.code domain deg)).card) :
    (∀ z : F, δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
      ReedSolomon.code domain deg) ≤ δ) ∧
    ∃ v : Fin l → Fin n → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      (∀ z, δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
        Curve.polynomialCurveEval (F := F) (A := F) v z) ≤ δ) ∧
      ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card ≤ δ * n := by
  classical
  set C : Set (Fin n → F) := (ReedSolomon.code domain deg : Set (Fin n → F)) with hC
  set δR : ℝ≥0 := (δ : ℝ≥0) with hδR
  suffices hja : jointAgreement (C := C) (δ := δR) (W := u) by
    obtain ⟨S, hScard, v, hv⟩ := hja
    have hvC : ∀ i, v i ∈ C := fun i => (hv i).1
    have hagree : ∀ i, ∀ x ∈ S, u i x = v i x := by
      intro i x hx
      have hmem := (hv i).2 hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem.symm
    -- `δ ≤ 1` (from the unique-decoding radius hypothesis, `(1-ρ)/2 ≤ 1/2 ≤ 1`).
    have hδ_le_one : δ ≤ 1 := by
      refine le_trans hδ ?_
      calc (1 - ρ (ReedSolomon.code domain deg)) / 2 ≤ (1 : ℚ≥0) / 2 := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            · exact tsub_le_self
          _ ≤ 1 := by norm_num
    have hSle : S.card ≤ n := by simpa using Finset.card_le_univ S
    -- Complement-card bound proven in `ℝ≥0` (real coefficient `δR`), stated with `ℕ`-subtraction
    -- on the left so it reflects cleanly back to `ℚ≥0`.
    have hcomplR : (((n - S.card : ℕ) : ℝ≥0)) ≤ δR * (n : ℝ≥0) := by
      have hcard : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by simp
      have h1 : (1 - δR) * (n : ℝ≥0) ≤ (S.card : ℝ≥0) := by rw [← hcard]; exact hScard
      have hδRle : δR ≤ 1 := by rw [hδR]; exact_mod_cast hδ_le_one
      have hexp : (1 - δR) * (n : ℝ≥0) = (n : ℝ≥0) - δR * (n : ℝ≥0) := by
        rw [tsub_mul, one_mul]
      rw [hexp] at h1
      have hδn_le : δR * (n : ℝ≥0) ≤ (n : ℝ≥0) := by
        calc δR * (n : ℝ≥0) ≤ 1 * (n : ℝ≥0) := by exact mul_le_mul_right' hδRle _
          _ = (n : ℝ≥0) := one_mul _
      have hsub := tsub_le_tsub_left h1 (n : ℝ≥0)
      rw [tsub_tsub_cancel_of_le hδn_le] at hsub
      calc (((n - S.card : ℕ)) : ℝ≥0) = (n : ℝ≥0) - (S.card : ℝ≥0) := by
            exact_mod_cast Nat.cast_tsub (α := ℝ≥0) n S.card
        _ ≤ δR * (n : ℝ≥0) := hsub
    -- `ℚ≥0` bound on `↑(n - #S : ℕ)`, routed through `ℕ`-casts (no truncated-ℚ≥0 subtraction).
    have hcomplNat : (((n - S.card : ℕ) : ℚ≥0)) ≤ δ * (n : ℚ≥0) := by
      have hRr : (((δ * (n : ℚ≥0) : ℚ≥0)) : ℝ≥0) = δR * (n : ℝ≥0) := by
        rw [hδR, NNRat.cast_mul]; push_cast; ring
      have hLr : ((((n - S.card : ℕ) : ℚ≥0)) : ℝ≥0) = (((n - S.card : ℕ) : ℝ≥0)) := by
        norm_cast
      have hkey : ((((n - S.card : ℕ) : ℚ≥0)) : ℝ≥0) ≤ (((δ * (n : ℚ≥0) : ℚ≥0)) : ℝ≥0) := by
        rw [hLr, hRr]; exact hcomplR
      exact_mod_cast hkey
    -- The disagreement set sits in `Sᶜ`.
    have hbadsub : ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _) ⊆ Sᶜ := by
      intro x hx
      have hx' : ∃ i, u i x ≠ v i x := by simpa using hx
      simp only [Finset.mem_compl]
      intro hxS
      obtain ⟨i, hne⟩ := hx'
      exact hne (hagree i x hxS)
    have hbadcard : ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card ≤ n - S.card := by
      calc ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card ≤ Sᶜ.card :=
            Finset.card_le_card hbadsub
        _ = n - S.card := by rw [Finset.card_compl]; simp
    -- Bound the disagreement of the two curves at each parameter by the coordinate
    -- disagreement set: the curve value at coordinate `x` depends only on the `x`-column,
    -- so if `u i x = v i x` for all `i`, the two curves agree at `x`.
    have hcurve_sub : ∀ z : F,
        (Finset.univ.filter
          (fun x : Fin n => Curve.polynomialCurveEval (F := F) (A := F) u z x
            ≠ Curve.polynomialCurveEval (F := F) (A := F) v z x))
        ⊆ ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _) := by
      intro z x hx
      rw [Finset.mem_filter] at hx
      have hxne := hx.2
      by_contra hcon
      have hall : ∀ i, u i x = v i x := by
        by_contra hc
        push_neg at hc
        exact hcon (by simpa using hc)
      exact hxne (by
        simp only [Curve.polynomialCurveEval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl (fun i _ => by rw [hall i]))
    -- Each `v`-curve point is a codeword (linear combination of codewords in a submodule).
    have hvcurve_mem : ∀ z : F,
        Curve.polynomialCurveEval (F := F) (A := F) v z ∈ ReedSolomon.code domain deg := by
      intro z
      simp only [Curve.polynomialCurveEval]
      exact Submodule.sum_smul_mem _ _ (fun i _ => by simpa [hC] using hvC i)
    -- Turn the cardinality bound into a relative-distance bound between the curves.
    have hbad_rel : ∀ z : F,
        δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
            Curve.polynomialCurveEval (F := F) (A := F) v z) ≤ δ := by
      intro z
      have hcardle : hammingDist (Curve.polynomialCurveEval (F := F) (A := F) u z)
            (Curve.polynomialCurveEval (F := F) (A := F) v z)
          ≤ ({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card := by
        rw [hammingDist]
        exact Finset.card_le_card (hcurve_sub z)
      have hcardQ : (hammingDist (Curve.polynomialCurveEval (F := F) (A := F) u z)
            (Curve.polynomialCurveEval (F := F) (A := F) v z) : ℚ≥0)
          ≤ δ * (n : ℚ≥0) := by
        calc (hammingDist _ _ : ℚ≥0)
            ≤ (({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card : ℚ≥0) := by
              exact_mod_cast hcardle
          _ ≤ ((n - S.card : ℕ) : ℚ≥0) := by exact_mod_cast hbadcard
          _ ≤ δ * (n : ℚ≥0) := hcomplNat
      unfold relHammingDist
      rw [div_le_iff₀ (by positivity)]
      have hn : (Fintype.card (Fin n) : ℚ≥0) = (n : ℚ≥0) := by simp
      rw [hn]
      exact hcardQ
    refine ⟨?_, v, hvC, ?_, ?_⟩
    · -- (a) every curve point is δ-close to the code, via the v-curve of codewords.
      intro z
      calc δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
            ReedSolomon.code domain deg)
          ≤ δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
              Curve.polynomialCurveEval (F := F) (A := F) v z) :=
            Code.relDistFromCode_le_relDist_to_mem _ _ (hvcurve_mem z)
        _ ≤ ((δ : ℚ≥0) : ENNReal) := by
            rw [show δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
                Curve.polynomialCurveEval (F := F) (A := F) v z)
                = ((relHammingDist (Curve.polynomialCurveEval (F := F) (A := F) u z)
                    (Curve.polynomialCurveEval (F := F) (A := F) v z) : ℚ≥0) : ENNReal) from rfl,
              ENNReal.coe_NNRat_coe_NNReal, ENNReal.coe_NNRat_coe_NNReal]
            exact_mod_cast hbad_rel z
    · -- (b)-2 the two curves are δ-close pointwise.
      exact hbad_rel
    · -- (b)-3 cardinality of the disagreement set.
      calc (({ x : Fin n | ∃ i, u i x ≠ v i x } : Finset _).card : ℚ≥0)
          ≤ ((n - S.card : ℕ) : ℚ≥0) := by exact_mod_cast hbadcard
        _ ≤ δ * (n : ℚ≥0) := hcomplNat
  -- Discharge the `jointAgreement` obligation via the proven Berlekamp-Welch engine.
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · -- Degenerate `l = 0`: the stack has no rows, so joint agreement holds vacuously on
    -- the full coordinate set (the `∀ i` obligation is over the empty index `Fin 0`).
    subst hl0
    refine ⟨Finset.univ, ?_, u, ?_⟩
    · simpa using
        mul_le_mul_right' (tsub_le_self : (1 : ℝ≥0) - δR ≤ 1) (Fintype.card (Fin n) : ℝ≥0)
    · exact fun i => (Fin.elim0 i)
  · -- Main case `l ≥ 1`: write `l = k + 1` and split on whether the code is trivial.
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    rcases Nat.eq_zero_or_pos deg with hdeg0 | hdegpos
    · -- `deg = 0`: trivial code `{0}`, outside the Berlekamp-Welch engine. The
      -- curve-hypothesis → jointAgreement implication for the trivial code is a genuinely
      -- separate §6.1 obligation: the naive coordinate double-count (`card_heavyCoords_mul_le`)
      -- fails to close it in the tight regime `⌊δn⌋ = δn`. Isolated as the single residual
      -- of Theorem 6.1 (baselined; NOT faked).
      subst hdeg0
      sorry
    · -- `deg ≥ 1`: discharge through the proven engine.
      haveI : NeZero deg := ⟨Nat.pos_iff_ne_zero.mp hdegpos⟩
      have := large_agreement_set_on_curve_jointAgreement_of_neZero
        (n := n) (k := k) (deg := deg) (domain := domain) (δ := δ) hδ u
        (by simpa [hC, Nat.add_sub_cancel] using hS)
      simpa [hC, hδR] using this

/-- Johnson regime; Theorem 6.2 of [BCIKS20]. As in the unique-decoding companion
`large_agreement_set_on_curve_implies_correlated_agreement`, `V` must be an actual Reed-Solomon
code (of rate `ρ`) rather than an arbitrary set of words. If the set of points on the curve
defined by `u` close to `V` has more than
`((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow ρ (3 / 2 : ℚ))) * n ^ 2 * (l - 1)`
points, then there exist vectors `v` from `V` that are `(1 - δ) * n` close to `u`. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement' {l : ℕ}
    [Finite F]
    {m : ℕ}
    {deg : ℕ}
    {domain : Fin n ↪ F}
    {δ : ℚ≥0}
    (hm : 3 ≤ m)
    (hδ : δ ≤ δ₀ (ρ (ReedSolomon.code domain deg)) m)
    {u : Fin l → Fin n → F}
    (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) /
        (3 * (Real.rpow (ρ (ReedSolomon.code domain deg)) (3 / 2 : ℚ)))
      * n ^ 2 * (l - 1) <
      (coeffs_of_close_proximity_curve (F := F) δ u (ReedSolomon.code domain deg)).card) :
    ∃ v : Fin l → Fin n → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
        (1 - δ) * n ≤ ({ x : Fin n | ∀ i, u i x = v i x } : Finset _).card := by
  sorry

end BCIKS20ProximityGapSection6

end ProximityGap
