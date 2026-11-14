/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.WeightedAgreement
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Extensions.Data.Probability.Instances
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Counterexamples to the removed BCIKS20 agreement axioms

Five former global axioms of the BCIKS20 cone are gone. In the current tree the corresponding
results are proved theorems of the canonical ArkLib modules, each with a positive-degree guard
`0 < deg`: `weighted_correlated_agreement_for_parameterized_curves`,
`weighted_correlated_agreement_over_affine_spaces` and their primed variants in
`WeightedAgreement.lean` (the affine-space ones sampling from
`Affine.affineSubspaceAtOrigin (u 0) (Fin.tail u)`), and
`large_agreement_set_on_curve_implies_correlated_agreement'` in `Curves.lean`. This file restates
the removed axioms as `Prop`s and proves them false, so that none of them can be reinstated in its
old form: the two weighted curve axioms as first stated, without the `0 < sqrtRate` guard they
later carried; the two affine-space axioms in their last, guarded form; and the Johnson-regime
axiom, which never had a guard.

* **Zero rate.** At `deg = 0` the Reed-Solomon code is `{0}` and its rate is `0`. Every threshold
  that divides by the rate or its square root is `0` under Lean's `x / 0 = 0`, so the hypotheses
  ask for a single good point, while a word with a nonzero coordinate never agrees with the zero
  codeword there. The witness is one coordinate of `ZMod 3` with `u 0 = 1` and `u 1 = -1`, whose
  curve vanishes at `z = 1`: `not_unguardedCurve`, `not_unguardedCurvePrimed` and
  `not_unguardedJohnsonCurves`. A positive-rate guard is therefore necessary; the proved theorems
  carry it as `0 < deg`.
* **Affine hull.** The two affine-space axioms sampled from `u 0 +ᵥ affineSpan F {u 1, …}`. For one
  direction this is the single point `u 0 + u 1`, the zero codeword when `u 1 = -u 0`, so the
  probability is `1`. Take `u 0 = (0, 1)` on the domain `{0, 1}` of `ZMod 1000003` and `deg = 1`,
  where the rate is `1/2` and the `0 < sqrtRate` guard holds. The conclusion would make the
  nonconstant `u 0` equal to a constant codeword on both coordinates: `not_affineHullSpaces` and
  `not_affineHullSpacesPrimed`. The proved theorems sample from
  `Affine.affineSubspaceAtOrigin (u 0) (Fin.tail u)`, that is `u 0 + span {u 1, …}`, instead.

These theorems refute the removed statements only; they say nothing about the guarded theorems
that replace them.
-/

open ProximityGap ProximityGap.WeightedAgreement NNReal
open scoped LinearCode ProbabilityTheory Pointwise

namespace ProximityGap.WeightedAgreement.Degenerate

/-! ### Probability helpers -/

/-- A uniform probability is `1` when the event holds at every point. -/
lemma prob_eq_one_of_forall {T : Type} [Fintype T] [Nonempty T] (P : T → Prop)
    (h : ∀ t, P t) : Pr_{let x ←$ᵖ T}[P x] = 1 := by
  classical
  rw [prob_tsum_form_singleton]
  simp only [h, if_true, mul_one]
  exact PMF.tsum_coe _

/-- A uniform probability is positive when the event holds at some point. -/
lemma prob_pos_of_mem {T : Type} [Fintype T] [Nonempty T] (P : T → Prop) (t : T)
    (ht : P t) : 0 < Pr_{let x ←$ᵖ T}[P x] := by
  classical
  rw [prob_tsum_form_singleton]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum t)
  simp [ht, PMF.uniformOfFintype_apply]

/-! ### Zero-rate fixture: one coordinate of `ZMod 3` -/

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- One coordinate in `ZMod 3`. -/
def dom : Fin 1 ↪ ZMod 3 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

lemma code_zero {w : Fin 1 → ZMod 3} (hw : w ∈ ReedSolomon.code dom 0) : w = 0 := by
  obtain ⟨y, hy, rfl⟩ := hw
  have : y = 0 := by simpa [Polynomial.mem_degreeLT] using hy
  subst this
  simp

lemma dim0 : LinearCode.dim (ReedSolomon.code (ι := Fin 1) (F := ZMod 3) dom 0) = 0 :=
  ReedSolomon.dim_eq_deg_of_le (ι := Fin 1) (F := ZMod 3) (α := dom) (by simp)

/-- At `deg = 0` the rate is `0`. -/
lemma rate_zero_deg : LinearCode.rate (ReedSolomon.code (ι := Fin 1) (F := ZMod 3) dom 0) = 0 := by
  unfold LinearCode.rate
  rw [dim0]
  simp

/-- At `deg = 0` the square-root rate is `0`, so the guard `0 < sqrtRate` excludes this case. -/
lemma sqrtRate_zero_deg : ReedSolomon.sqrtRate (ι := Fin 1) (F := ZMod 3) 0 dom = 0 := by
  unfold ReedSolomon.sqrtRate LinearCode.rate
  rw [dim0]
  simp

lemma finCarrier_zero_deg :
    ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0 = {0} := by
  ext w
  simp only [ReedSolomon.finCarrier, Set.mem_toFinset, Finset.mem_singleton]
  constructor
  · intro h; exact code_zero h
  · rintro rfl; exact Submodule.zero_mem _

/-- `u 0 = 1`, `u 1 = -1`, so `u 0 + 1 • u 1 = 0`. -/
def u : Fin (0 + 2) → Fin 1 → ZMod 3 := ![fun _ => 1, fun _ => -1]

/-- Unit weights. -/
def mu : Fin 1 → Set.Icc (0 : ℚ) 1 := fun _ => ⟨1, by simp⟩

lemma agree_zero_ge : (1 : ℝ) ≤ agree_set mu (0 : Fin 1 → ZMod 3)
    (ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0) := by
  have h0 : (0 : Fin 1 → ZMod 3) ∈
      ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0 := by
    rw [finCarrier_zero_deg]; simp
  have := Finset.le_max' (Finset.image (agree mu (0 : Fin 1 → ZMod 3))
    (ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0)) (agree mu 0 0)
    (Finset.mem_image_of_mem _ h0)
  refine le_trans ?_ this
  simp [agree, mu]

/-- The fixture curve vanishes at `z = 1`. -/
lemma curve_one_eq_zero : Curve.polynomialCurveEval (F := ZMod 3) (A := ZMod 3) u 1 = 0 := by
  funext i
  simp [Curve.polynomialCurveEval, u]

/-- At `deg = 0` the error bound vanishes at `δ = 1`: it lies in neither the unique-decoding
interval `[0, 1/2]` nor the open Johnson interval `(1/2, 1)`. -/
lemma errorBound_one_zero_deg :
    ProximityGap.errorBound (ι := Fin 1) (F := ZMod 3) 1 0 dom = 0 := by
  have hc : ((LinearCode.rate (ReedSolomon.code (ι := Fin 1) (F := ZMod 3) dom 0) : ℚ≥0) :
      ℝ≥0) = 0 := by
    rw [rate_zero_deg]; simp
  have h1 : ¬ ((1 : ℝ≥0) ∈ Set.Icc 0 ((1 - (0 : ℝ≥0)) / 2)) := by
    rintro ⟨-, h⟩
    rw [← NNReal.coe_le_coe] at h
    norm_num at h
  have h2 : ¬ ((1 : ℝ≥0) ∈ Set.Ioo ((1 - (0 : ℝ≥0)) / 2) (1 - NNReal.sqrt 0)) := by
    rintro ⟨-, h⟩
    simp at h
  unfold ProximityGap.errorBound
  simp only [hc, h1, h2, ↓reduceIte]

/-- No coordinate of the fixture agrees with a degree-`0` codeword in its first word. -/
lemma not_agree_first {v : Fin (0 + 2) → Fin 1 → ZMod 3}
    (hv : ∀ i, v i ∈ ReedSolomon.code dom 0) (x : Fin 1) : u 0 x ≠ v 0 x := by
  rw [code_zero (hv 0)]
  simp [u]

/-! ### Zero rate: the weighted curve statements -/

/-- The removed axiom `weighted_correlated_agreement_for_parameterized_curves` as it was first
stated, without the `0 < sqrtRate` guard. -/
def UnguardedCurve : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {l : ℕ} {u : Fin (l + 2) → ι → F} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {μ : ι → Set.Icc (0 : ℚ) 1} {M : ℕ} {α : ℝ≥0},
    (∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
    letI sqrtRate := ReedSolomon.sqrtRate deg domain
    sqrtRate < α →
    α < 1 →
    letI ε := ProximityGap.errorBound δ deg domain
    letI pr :=
      let curvePts := Curve.polynomialCurveFinite (F := F) (A := F) u
      Pr_{let y ←$ᵖ curvePts}[agree_set μ y (ReedSolomon.finCarrier domain deg) ≥ α]
    pr > (l + 1 : NNReal) * ε →
    pr ≥
      ENNReal.ofReal (
        ((l + 1) * (M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
        *
        (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
      ) →
    ∃ ι' : Finset ι, ∃ v : Fin (l + 2) → ι → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      mu_set μ ι' ≥ α ∧
      ∀ i, ∀ x ∈ ι', u i x = v i x

/-- The unguarded unprimed curve statement is false: it is refuted at `deg = 0` with `δ = 1`,
where `errorBound 1 0 dom = 0` and the field-size threshold is `0`. -/
theorem not_unguardedCurve : ¬ UnguardedCurve := by
  classical
  intro hax
  have hsq := sqrtRate_zero_deg
  have hpt : (0 : Fin 1 → ZMod 3) ∈ Curve.polynomialCurveFinite (F := ZMod 3) (A := ZMod 3) u := by
    simp only [Curve.polynomialCurveFinite, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, curve_one_eq_zero.symm⟩
  obtain ⟨ι', v, hv, hmu, hagree⟩ := hax (ι := Fin 1) (F := ZMod 3) (l := 0) (u := u) (deg := 0)
    (domain := dom) (δ := 1) (μ := mu) (M := 1) (α := 1 / 2) (fun _ => ⟨1, by simp [mu]⟩)
    (by rw [hsq]; norm_num) (by norm_num)
    (by
      simp only [errorBound_one_zero_deg, ENNReal.coe_zero, mul_zero]
      exact prob_pos_of_mem _ ⟨0, hpt⟩ (le_trans (by norm_num) agree_zero_ge))
    (by simp [hsq])
  have hempty : ι' = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    exact not_agree_first hv x (hagree 0 x hx)
  rw [hempty] at hmu
  norm_num [mu_set] at hmu

/-- The removed axiom `weighted_correlated_agreement_for_parameterized_curves'` as it was first
stated, without the `0 < sqrtRate` guard. -/
def UnguardedCurvePrimed : Prop :=
  ∀ {ι : Type} [Fintype ι] {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {l : ℕ} {u : Fin (l + 2) → ι → F}
    {deg : ℕ} {domain : ι ↪ F}
    {μ : ι → Set.Icc (0 : ℚ) 1} {M m : ℕ},
    3 ≤ m →
    (∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
    ∀ {α : ℝ≥0},
    ReedSolomon.sqrtRate deg domain * (1 + 1 / (2 * m : ℝ)) ≤ α →
    (Finset.card ({z : F | agree_set μ (Curve.polynomialCurveEval (F := F) (A := F) u z)
        (ReedSolomon.finCarrier domain deg) ≥ α} : Finset F) : ℝ) >
      max ((1 + 1 / (2 * m : ℝ)) ^ 7 * m ^ 7 * (Fintype.card ι) ^ 2 * (l + 1) /
            (3 * (ReedSolomon.sqrtRate deg domain : ℝ) ^ 3))
          ((2 * m + 1) * (M * Fintype.card ι + 1) * (l + 1) /
            (ReedSolomon.sqrtRate deg domain).toReal) →
    ∃ v : Fin (l + 2) → ι → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      mu_set μ { i : ι | ∀ j, u j i = v j i } ≥ α

/-- The unguarded statement is false: it is refuted at `deg = 0`. -/
theorem not_unguardedCurvePrimed : ¬ UnguardedCurvePrimed := by
  intro hax
  have hsq := sqrtRate_zero_deg
  have h := hax (ι := Fin 1) (F := ZMod 3) (l := 0) (u := u) (deg := 0)
    (domain := dom) (μ := mu) (M := 1) (m := 3) (by norm_num) (fun i => ⟨1, by simp [mu]⟩)
    (α := 1 / 2) (by simp [hsq]) (by
      rw [hsq]
      simp only [Nat.reduceAdd, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        pow_zero, one_smul, Nat.mod_succ, pow_one, one_div, NNReal.coe_inv, NNReal.coe_ofNat,
        ge_iff_le, Nat.cast_ofNat, mul_inv_rev, Fintype.card_unique, Nat.cast_one, one_pow,
        mul_one, CharP.cast_eq_zero, zero_add, coe_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, div_zero, max_self, gt_iff_lt, Nat.cast_pos,
        Finset.card_pos]
      refine ⟨1, ?_⟩
      have e : u 0 + (1 : ZMod 3) • u 1 = 0 := by
        funext i; simp [u]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show ((2 : ℝ)⁻¹) ≤ agree_set mu (u 0 + (1 : ZMod 3) • u 1)
        (ReedSolomon.finCarrier (ι := Fin 1) (F := ZMod 3) dom 0)
      rw [e]
      exact le_trans (by norm_num) agree_zero_ge)
  obtain ⟨v, hv, hmu⟩ := h
  have h0 : v 0 0 = 0 := by
    have := code_zero (hv 0); simp [this]
  have hempty : ({i : Fin 1 | ∀ j : Fin (0 + 2), u j i = v j i} : Finset (Fin 1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    have hh : ∀ j : Fin (0 + 2), u j i = v j i := (Finset.mem_filter.mp hi).2
    have := hh 0
    have hi' : i = 0 := Subsingleton.elim _ _
    subst hi'
    rw [h0] at this
    simp [u] at this
  rw [hempty] at hmu
  simp [mu_set] at hmu
  norm_num at hmu

/-! ### Zero rate: the Johnson-regime curve statement -/

/-- The removed axiom `large_agreement_set_on_curve_implies_correlated_agreement'` of
`Curves.lean`, which had no positive-rate guard. -/
def UnguardedJohnsonCurves : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n] {l : ℕ} [Finite F]
    {m deg : ℕ} {domain : Fin n ↪ F} {δ : ℚ≥0},
    3 ≤ m →
    δ ≤ δ₀ (ρ (ReedSolomon.code domain deg)) m →
    ∀ {u : Fin l → Fin n → F},
    ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) /
        (3 * (Real.rpow (ρ (ReedSolomon.code domain deg)) (3 / 2 : ℚ))) * n ^ 2 * (l - 1) <
      (coeffs_of_close_proximity_curve (F := F) δ u (ReedSolomon.toFinset domain deg)).card →
    ∃ v : Fin l → Fin n → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
        (1 - δ) * n ≤ ({ x : Fin n | ∀ i, u i x = v i x } : Finset _).card

/-- The unguarded Johnson-regime statement is false: at `deg = 0` with `δ = 0` the threshold
divides by `Real.rpow 0 (3 / 2) = 0`, so the single good parameter `z = 1` meets it. -/
theorem not_unguardedJohnsonCurves : ¬ UnguardedJohnsonCurves := by
  classical
  intro hax
  have hρ := rate_zero_deg
  have hS : (1 : ZMod 3) ∈ coeffs_of_close_proximity_curve (F := ZMod 3) (n := 1) (0 : ℚ≥0) u
      (ReedSolomon.toFinset dom 0) := by
    simp only [coeffs_of_close_proximity_curve, Set.mem_toFinset, Set.mem_setOf_eq]
    rw [curve_one_eq_zero]
    refine le_trans (Code.relDistFromCode_le_relDist_to_mem _ 0
      (by simp [ReedSolomon.toFinset])) ?_
    simp [Code.relHammingDist]
    rw [NNRat.cast, NNRatCast.nnratCast, ENNReal.instNNRatCast]
    simp
  obtain ⟨v, hv, hcard⟩ := hax (F := ZMod 3) (n := 1) (l := 0 + 2) (m := 3) (deg := 0)
    (domain := dom) (δ := 0) (by norm_num) (by rw [hρ]; norm_num [δ₀]) (u := u) (by
      rw [hρ]
      norm_num [Real.rpow_eq_pow, Real.zero_rpow]
      exact ⟨1, by simpa using hS⟩)
  have hempty : ({x : Fin 1 | ∀ i, u i x = v i x} : Finset (Fin 1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    exact not_agree_first hv x ((Finset.mem_filter.mp hx).2 0)
  rw [hempty] at hcard
  norm_num at hcard

/-! ### Positive-rate fixture: the domain `{0, 1}` of `ZMod 1000003` -/

/-- The prime field size of the positive-rate affine-hull counterexamples. -/
abbrev bigP : ℕ := 1000003

instance : Fact (Nat.Prime bigP) := ⟨by norm_num⟩

/-- The two-point domain `{0, 1}`. -/
def dom2 : Fin 2 ↪ ZMod bigP :=
  ⟨![0, 1], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

/-- `v2 0 = (0, 1)` is not constant and `v2 1 = -v2 0`, so `v2 0 + v2 1 = 0`. -/
def v2 : Fin (0 + 2) → Fin 2 → ZMod bigP := ![![0, 1], ![0, -1]]

/-- Unit weights on two coordinates. -/
def mu2 : Fin 2 → Set.Icc (0 : ℚ) 1 := fun _ => ⟨1, by simp⟩

/-- A Reed-Solomon codeword of degree `< 1` is constant. -/
lemma code_one_const {w : Fin 2 → ZMod bigP} (hw : w ∈ ReedSolomon.code dom2 1) :
    w 0 = w 1 := by
  obtain ⟨p, hp, rfl⟩ := hw
  have hdeg : p.degree ≤ 0 :=
    Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using Polynomial.mem_degreeLT.mp hp)
  rw [Polynomial.eq_C_of_degree_le_zero hdeg]
  simp [ReedSolomon.evalOnPoints]

lemma rate_one : LinearCode.rate (ReedSolomon.code dom2 1) = 1 / 2 := by
  rw [ReedSolomon.rateOfLinearCode_eq_min_div]
  norm_num

lemma sqrtRate_one : ReedSolomon.sqrtRate 1 dom2 = NNReal.sqrt (1 / 2) := by
  unfold ReedSolomon.sqrtRate
  rw [rate_one]
  norm_num

lemma two_thirds_le_sqrt_half : (2 / 3 : ℝ≥0) ≤ NNReal.sqrt (1 / 2) :=
  NNReal.le_sqrt_iff_sq_le.mpr (by rw [← NNReal.coe_le_coe]; norm_num)

lemma sqrt_half_le_three_quarters : NNReal.sqrt (1 / 2) ≤ 3 / 4 :=
  NNReal.sqrt_le_iff_le_sq.mpr (by rw [← NNReal.coe_le_coe]; norm_num)

lemma two_thirds_le_real_sqrt_half : (2 / 3 : ℝ) ≤ √(1 / 2) :=
  Real.le_sqrt_of_sq_le (by norm_num)

lemma real_sqrt_half_le_three_quarters : √(1 / 2 : ℝ) ≤ 3 / 4 :=
  (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)

lemma nine_tenths_le_one : (9 / 10 : ℝ≥0) ≤ 1 := by
  rw [← NNReal.coe_le_coe]; norm_num

/-- At rate `1/2` the agreement parameter `9/10`, read as a distance, lies outside both regimes of
`errorBound`, which is therefore `0`. -/
lemma errorBound_nine_tenths : ProximityGap.errorBound (9 / 10) 1 dom2 = 0 := by
  have hs := two_thirds_le_sqrt_half
  have hc : ((LinearCode.rate (ReedSolomon.code dom2 1) : ℚ≥0) : ℝ≥0) = 1 / 2 := by
    rw [rate_one]; norm_num
  have h1 : ¬ ((9 / 10 : ℝ≥0) ∈ Set.Icc 0 ((1 - (1 / 2 : ℝ≥0)) / 2)) := by
    rintro ⟨-, h⟩
    rw [← NNReal.coe_le_coe] at h
    norm_num at h
  have h2 : ¬ ((9 / 10 : ℝ≥0) ∈ Set.Ioo ((1 - (1 / 2 : ℝ≥0)) / 2) (1 - NNReal.sqrt (1 / 2))) := by
    rintro ⟨-, h⟩
    have : (1 : ℝ≥0) - NNReal.sqrt (1 / 2) ≤ 1 / 3 := by
      rw [tsub_le_iff_right]
      calc (1 : ℝ≥0) = 1 / 3 + 2 / 3 := by rw [← NNReal.coe_inj]; norm_num
        _ ≤ 1 / 3 + NNReal.sqrt (1 / 2) := by gcongr
    have h910 : (1 / 3 : ℝ≥0) < 9 / 10 := by rw [← NNReal.coe_lt_coe]; norm_num
    exact lt_irrefl _ (lt_of_lt_of_le h (this.trans h910.le))
  unfold ProximityGap.errorBound
  simp only [hc, h1, h2, ↓reduceIte]

/-- The positive-rate fixture: at `deg = 1` the conclusion would make the nonconstant `v2 0` agree
with a constant codeword on both coordinates. -/
lemma not_agree_both {w : Fin (0 + 2) → Fin 2 → ZMod bigP}
    (hw : ∀ i, w i ∈ ReedSolomon.code dom2 1) (h0 : v2 0 0 = w 0 0) (h1 : v2 0 1 = w 0 1) :
    False := by
  have hc := code_one_const (hw 0)
  rw [← h0, ← h1] at hc
  simp [v2] at hc

/-- A subset of the two coordinates of unit-weight measure `> 1/2` is everything. -/
lemma eq_univ_of_mu_set {s : Finset (Fin 2)} (hs : (1 / 2 : ℝ) < mu_set mu2 s) :
    s = Finset.univ := by
  apply Finset.eq_univ_of_card
  have hle : s.card ≤ 2 := by simpa using Finset.card_le_univ s
  have hcard : 1 < s.card := by
    simp only [mu_set, mu2, Fintype.card_fin] at hs
    norm_num at hs
    exact_mod_cast hs
  simp only [Fintype.card_fin]
  omega

/-- Every point of the translated affine hull of the one direction `v2 1` is `v2 0 + v2 1 = 0`. -/
lemma hull_eq_zero {y : Fin 2 → ZMod bigP}
    (hy : y ∈ v2 0 +ᵥ affineSpan (ZMod bigP)
      (((Finset.univ.image (Fin.tail v2) : Finset (Fin 2 → ZMod bigP)) :
        Set (Fin 2 → ZMod bigP)))) :
    y = 0 := by
  have himg : (Finset.univ.image (Fin.tail v2) : Finset (Fin 2 → ZMod bigP)) = {v2 1} := by
    ext w
    simp [Fin.tail]
  rw [himg, Finset.coe_singleton] at hy
  have hy' : y ∈ v2 0 +ᵥ ((affineSpan (ZMod bigP) {v2 1} :
      AffineSubspace (ZMod bigP) (Fin 2 → ZMod bigP)) : Set (Fin 2 → ZMod bigP)) := hy
  obtain ⟨x, hx, rfl⟩ := Set.mem_vadd_set.mp hy'
  have hx' : x = v2 1 := (AffineSubspace.mem_affineSpan_singleton _ _).mp hx
  subst hx'
  funext i
  fin_cases i <;> simp [v2]

/-- The zero word has full unit-weight agreement with the degree-`1` code. -/
lemma one_le_agree_set_zero2 :
    (1 : ℝ) ≤ agree_set mu2 (0 : Fin 2 → ZMod bigP) (ReedSolomon.finCarrier dom2 1) := by
  have h0 : (0 : Fin 2 → ZMod bigP) ∈ ReedSolomon.finCarrier dom2 1 := by
    simp only [ReedSolomon.finCarrier, Set.mem_toFinset]
    exact Submodule.zero_mem _
  refine le_trans ?_ (Finset.le_max' (Finset.image (agree mu2 (0 : Fin 2 → ZMod bigP))
    (ReedSolomon.finCarrier dom2 1)) (agree mu2 0 0) (Finset.mem_image_of_mem _ h0))
  simp [agree, mu2]

/-- Every point of the translated affine hull of the fixture has unit-weight agreement at least
`α ≤ 1` with the degree-`1` code. -/
lemma hull_event {α : ℝ≥0} (hα : α ≤ 1) {y : Fin 2 → ZMod bigP}
    (hy : y ∈ v2 0 +ᵥ affineSpan (ZMod bigP)
      (((Finset.univ.image (Fin.tail v2) : Finset (Fin 2 → ZMod bigP)) :
        Set (Fin 2 → ZMod bigP)))) :
    agree_set mu2 y (ReedSolomon.finCarrier dom2 1) ≥ α := by
  rw [hull_eq_zero hy]
  exact le_trans (by exact_mod_cast hα) one_le_agree_set_zero2

/-! ### Affine hull: the weighted affine-space statements -/

/-- The removed axiom `weighted_correlated_agreement_over_affine_spaces` in its last form: with the
`0 < sqrtRate` guard, but sampling from the translated affine hull `u 0 +ᵥ affineSpan F {u 1, …}`.
Its original unguarded form implies this one. -/
def AffineHullSpaces : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {l : ℕ} {u : Fin (l + 2) → ι → F} {deg : ℕ} {domain : ι ↪ F} {μ : ι → Set.Icc (0 : ℚ) 1}
    {M : ℕ} {α : ℝ≥0},
    0 < ReedSolomon.sqrtRate deg domain →
    letI sqrtRate := ReedSolomon.sqrtRate deg domain
    sqrtRate < α →
    α < 1 →
    (∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
    letI ε := ProximityGap.errorBound α deg domain
    letI pr :=
      let spacePts :=
        u 0 +ᵥ affineSpan F (((Finset.univ.image (Fin.tail u) : Finset (ι → F)) : Set (ι → F)))
      Pr_{let y ←$ᵖ spacePts}[agree_set μ y (ReedSolomon.finCarrier domain deg) ≥ α]
    pr > ε →
    pr ≥ ENNReal.ofReal (
      ((M * Fintype.card ι + 1) : ℝ) / (Fintype.card F : ℝ)
      *
      (1 / min (α - sqrtRate) (sqrtRate / 20) + 3 / sqrtRate)
    ) →
    ∃ ι' : Finset ι, ∃ v : Fin (l + 2) → ι → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      mu_set μ ι' ≥ α ∧
      ∀ i, ∀ x ∈ ι', u i x = v i x

/-- The affine-hull statement is false even at positive rate: the hull is the single codeword
`0`, the probability is `1`, and both thresholds are below `1`. -/
theorem not_affineHullSpaces : ¬ AffineHullSpaces := by
  classical
  intro hax
  have hs := sqrtRate_one
  have hlo := two_thirds_le_sqrt_half
  have hhi := sqrt_half_le_three_quarters
  obtain ⟨ι', w, hw, hmu, hagree⟩ := hax (ι := Fin 2) (F := ZMod bigP) (l := 0) (u := v2)
    (deg := 1) (domain := dom2) (μ := mu2) (M := 1) (α := 9 / 10)
    (by rw [hs]; exact lt_of_lt_of_le (by norm_num) hlo)
    (by rw [hs]; exact lt_of_le_of_lt hhi (by norm_num))
    (by norm_num)
    (fun _ => ⟨1, by simp [mu2]⟩)
    (by
      try dsimp only
      rw [prob_eq_one_of_forall]
      · rw [errorBound_nine_tenths]; simp
      · exact fun y => hull_event nine_tenths_le_one y.2)
    (by
      try dsimp only
      rw [prob_eq_one_of_forall]
      swap
      · exact fun y => hull_event nine_tenths_le_one y.2
      rw [hs]
      refine ENNReal.ofReal_le_one.mpr ?_
      set s := NNReal.sqrt (1 / 2) with hs_def
      have hsR : (2 / 3 : ℝ) ≤ (s : ℝ) := by
        calc (2 / 3 : ℝ) = ((2 / 3 : ℝ≥0) : ℝ) := by norm_num
          _ ≤ (s : ℝ) := NNReal.coe_le_coe.mpr hlo
      have hmin : (1 / 30 : ℝ≥0) ≤ min (9 / 10 - s) (s / 20) := by
        refine le_min ?_ ?_
        · rw [le_tsub_iff_right (hhi.trans (by rw [← NNReal.coe_le_coe]; norm_num))]
          calc (1 / 30 : ℝ≥0) + s ≤ 1 / 30 + 3 / 4 := by gcongr
            _ ≤ 9 / 10 := by rw [← NNReal.coe_le_coe]; norm_num
        · rw [le_div_iff₀ (by positivity)]
          calc (1 / 30 : ℝ≥0) * 20 = 2 / 3 := by rw [← NNReal.coe_inj]; norm_num
            _ ≤ s := hlo
      have hminR : (1 / 30 : ℝ) ≤ ((min (9 / 10 - s) (s / 20) : ℝ≥0) : ℝ) := by
        calc (1 / 30 : ℝ) = ((1 / 30 : ℝ≥0) : ℝ) := by norm_num
          _ ≤ _ := NNReal.coe_le_coe.mpr hmin
      have hpos : (0 : ℝ) < ((min (9 / 10 - s) (s / 20) : ℝ≥0) : ℝ) :=
        lt_of_lt_of_le (by norm_num) hminR
      have hspos : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le (by norm_num) hsR
      have h1 : 1 / ((min (9 / 10 - s) (s / 20) : ℝ≥0) : ℝ) ≤ 30 := by
        rw [div_le_iff₀ hpos]; linarith
      have h2 : 3 / (s : ℝ) ≤ 9 / 2 := by
        rw [div_le_iff₀ hspos]; linarith
      simp only [Fintype.card_fin, ZMod.card, Nat.cast_one, one_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)) ?_
      norm_num [bigP])
  have huniv := eq_univ_of_mu_set (lt_of_lt_of_le (by norm_num [NNReal.coe_div]) hmu)
  subst huniv
  exact not_agree_both hw (hagree 0 0 (Finset.mem_univ _)) (hagree 0 1 (Finset.mem_univ _))

/-- The removed axiom `weighted_correlated_agreement_over_affine_spaces'` in its last form: with
the `0 < sqrtRate` guard, but sampling from the translated affine hull. Its original unguarded
form implies this one. -/
def AffineHullSpacesPrimed : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {l : ℕ} {u : Fin (l + 2) → ι → F} {deg : ℕ} {domain : ι ↪ F} {μ : ι → Set.Icc (0 : ℚ) 1}
    {α : ℝ≥0} {M m : ℕ},
    3 ≤ m →
    (∀ i, ∃ n : ℤ, (μ i).1 = (n : ℚ) / (M : ℚ)) →
    0 < ReedSolomon.sqrtRate deg domain →
    letI sqrtRate := ReedSolomon.sqrtRate deg domain
    letI pr :=
      let spacePts :=
        u 0 +ᵥ affineSpan F (((Finset.univ.image (Fin.tail u) : Finset (ι → F)) : Set (ι → F)))
      Pr_{let y ←$ᵖ spacePts}[agree_set μ y (ReedSolomon.finCarrier domain deg) ≥ α]
    sqrtRate * (1 + 1 / (2 * m : ℝ)) ≤ α →
    letI numeratorl : ℝ := (1 + 1 / (2 * m : ℝ)) ^ 7 * m ^ 7 * (Fintype.card ι) ^ 2
    letI denominatorl : ℝ := (3 * sqrtRate ^ 3) * Fintype.card F
    letI numeratorr : ℝ := (2 * m + 1) * (M * Fintype.card ι + 1)
    letI denominatorr : ℝ := sqrtRate * Fintype.card F
    pr > ENNReal.ofReal (max (numeratorl / denominatorl) (numeratorr / denominatorr)) →
    ∃ v : Fin (l + 2) → ι → F,
      (∀ i, v i ∈ ReedSolomon.code domain deg) ∧
      mu_set μ { i : ι | ∀ j, u j i = v j i } ≥ α

/-- The primed affine-hull statement is false even at positive rate (`m = 3`, `α = 1`). -/
theorem not_affineHullSpacesPrimed : ¬ AffineHullSpacesPrimed := by
  classical
  intro hax
  have hs := sqrtRate_one
  have hlo := two_thirds_le_sqrt_half
  have hsR := two_thirds_le_real_sqrt_half
  have hsR' := real_sqrt_half_le_three_quarters
  obtain ⟨w, hw, hmu⟩ := hax (ι := Fin 2) (F := ZMod bigP) (l := 0) (u := v2) (deg := 1)
    (domain := dom2) (μ := mu2) (α := 1) (M := 1) (m := 3) (by norm_num)
    (fun _ => ⟨1, by simp [mu2]⟩)
    (by rw [hs]; exact lt_of_lt_of_le (by norm_num) hlo)
    (by
      rw [hs]
      push_cast
      linarith)
    (by
      try dsimp only
      rw [prob_eq_one_of_forall]
      swap
      · exact fun y => hull_event le_rfl y.2
      rw [hs]
      refine ENNReal.ofReal_lt_one.mpr ?_
      have hcube : (8 / 27 : ℝ) ≤ √(1 / 2 : ℝ) ^ 3 := by
        calc (8 / 27 : ℝ) = (2 / 3) ^ 3 := by norm_num
          _ ≤ √(1 / 2 : ℝ) ^ 3 := by gcongr
      simp only [Fintype.card_fin, ZMod.card, bigP]
      push_cast
      refine max_lt ?_ ?_
      · rw [div_lt_one (by positivity)]
        nlinarith [hcube]
      · rw [div_lt_one (by positivity)]
        nlinarith [hsR])
  have huniv := eq_univ_of_mu_set (lt_of_lt_of_le (by norm_num) hmu)
  have h0 : (0 : Fin 2) ∈ ({i : Fin 2 | ∀ j, v2 j i = w j i} : Finset (Fin 2)) := by
    rw [huniv]; exact Finset.mem_univ _
  have h1 : (1 : Fin 2) ∈ ({i : Fin 2 | ∀ j, v2 j i = w j i} : Finset (Fin 2)) := by
    rw [huniv]; exact Finset.mem_univ _
  exact not_agree_both hw ((Finset.mem_filter.mp h0).2 0) ((Finset.mem_filter.mp h1).2 0)

end ProximityGap.WeightedAgreement.Degenerate
