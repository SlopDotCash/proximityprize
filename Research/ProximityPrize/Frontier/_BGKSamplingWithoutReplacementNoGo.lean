/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Sampling without replacement does not control the injective depth-seven transform

For a finite phase family `w : ι → ℂ`, compare

* the with-replacement transform `(∑ x, w x)^r`, a sum over all functions `Fin r → ι`; and
* the without-replacement transform, a sum over injective functions `Fin r → ι`.

The two differ by exactly the sum over repeated tuples.  If every phase has norm one, the triangle
inequality therefore gives the sharp coupling envelope

`‖D_r(w) - (∑ x, w x)^r‖ ≤ |ι|^r - |ι|.descFactorial r`.

The envelope is attained by aligned phases.  At depth seven and production size `n=2^30`, the
error has bit length `185`; its square exceeds the coefficient-`126871` per-frequency target
`126871*n^7` by more than `2^141`.  Thus a generic sampling-without-replacement or Maclaurin
argument loses over 141 energy bits before using any subgroup structure.  This does not rule out
a subgroup-specific exterior estimate; it proves that phase norms, distinct sampling, and the
ordinary period alone do not supply one.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKSamplingWithoutReplacementNoGo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All ordered `r`-tuples. -/
noncomputable def allTuples (r : Nat) : Finset (Fin r → ι) := Finset.univ

/-- Ordered `r`-tuples with distinct coordinates. -/
noncomputable def injectiveTuples (r : Nat) : Finset (Fin r → ι) :=
  Finset.univ.filter Function.Injective

/-- Ordered `r`-tuples having at least one repeated coordinate. -/
noncomputable def repeatedTuples (r : Nat) : Finset (Fin r → ι) :=
  Finset.univ.filter fun f => ¬Function.Injective f

/-- Phase monomial associated to one ordered tuple. -/
noncomputable def tupleMonomial (w : ι → Complex) {r : Nat} (f : Fin r → ι) : Complex :=
  ∏ i, w (f i)

/-- With-replacement transform. -/
noncomputable def allTupleTransform (w : ι → Complex) (r : Nat) : Complex :=
  ∑ f : Fin r → ι, tupleMonomial w f

/-- Without-replacement/injective transform. -/
noncomputable def injectiveTupleTransform (w : ι → Complex) (r : Nat) : Complex :=
  ∑ f ∈ injectiveTuples r, tupleMonomial w f

/-- Repeated-coordinate correction. -/
noncomputable def repeatedTupleTransform (w : ι → Complex) (r : Nat) : Complex :=
  ∑ f ∈ repeatedTuples r, tupleMonomial w f

/-- All tuples partition into injective and repeated tuples. -/
theorem allTupleTransform_eq_injective_add_repeated (w : ι → Complex) (r : Nat) :
    allTupleTransform w r =
      injectiveTupleTransform w r + repeatedTupleTransform w r := by
  classical
  simpa only [allTupleTransform, injectiveTupleTransform, repeatedTupleTransform,
    injectiveTuples, repeatedTuples] using
    (Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin r → ι)) Function.Injective
      (fun f => tupleMonomial w f)).symm

/-- The with-replacement transform is the `r`th power of the ordinary phase sum. -/
theorem allTupleTransform_eq_sum_pow (w : ι → Complex) (r : Nat) :
    allTupleTransform w r = (∑ x, w x) ^ r := by
  unfold allTupleTransform tupleMonomial
  rw [Fintype.sum_pow]

/-- The number of injective ordered tuples is the descending factorial. -/
noncomputable def injectiveTuplesEquivEmbedding (r : Nat) :
    {f // f ∈ injectiveTuples (ι := ι) r} ≃ (Fin r ↪ ι) where
  toFun f :=
    ⟨f.1, (Finset.mem_filter.mp f.2).2⟩
  invFun f :=
    ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.injective⟩⟩
  left_inv f := by ext i; rfl
  right_inv f := by ext i; rfl

theorem card_injectiveTuples (r : Nat) :
    (injectiveTuples (ι := ι) r).card = (Fintype.card ι).descFactorial r := by
  classical
  rw [← Fintype.card_coe, Fintype.card_congr (injectiveTuplesEquivEmbedding r),
    Fintype.card_embedding_eq]
  simp

/-- The number of repeated tuples is the difference between all and injective tuple counts. -/
theorem card_repeatedTuples (r : Nat) :
    (repeatedTuples (ι := ι) r).card =
      (Fintype.card ι) ^ r - (Fintype.card ι).descFactorial r := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin r → ι))) Function.Injective
  have hrev :
      (repeatedTuples (ι := ι) r).card + (injectiveTuples (ι := ι) r).card =
        (Finset.univ : Finset (Fin r → ι)).card := by
    simpa [repeatedTuples, injectiveTuples, add_comm] using hpart
  rw [card_injectiveTuples] at hrev
  simpa [Fintype.card_pi_const] using
    (eq_tsub_of_add_eq hrev)

/-- A unit-modulus phase monomial again has norm one. -/
theorem norm_tupleMonomial_eq_one (w : ι → Complex)
    (hw : ∀ x, ‖w x‖ = 1) {r : Nat} (f : Fin r → ι) :
    ‖tupleMonomial w f‖ = 1 := by
  unfold tupleMonomial
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => hw (f i)

/-- Sharp triangle envelope for the repeated-coordinate correction. -/
theorem norm_repeatedTupleTransform_le (w : ι → Complex)
    (hw : ∀ x, ‖w x‖ = 1) (r : Nat) :
    ‖repeatedTupleTransform w r‖ ≤
      (((Fintype.card ι) ^ r - (Fintype.card ι).descFactorial r : Nat) : Real) := by
  classical
  unfold repeatedTupleTransform
  calc
    ‖∑ f ∈ repeatedTuples r, tupleMonomial w f‖
        ≤ ∑ f ∈ repeatedTuples r, ‖tupleMonomial w f‖ := norm_sum_le _ _
    _ = ∑ _f ∈ repeatedTuples r, (1 : Real) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact norm_tupleMonomial_eq_one w hw f
    _ = (repeatedTuples (ι := ι) r).card := by simp
    _ = (((Fintype.card ι) ^ r - (Fintype.card ι).descFactorial r : Nat) : Real) := by
      rw [card_repeatedTuples]

/-- **Sampling-without-replacement coupling.**  The injective transform differs from the `r`th
power of the ordinary phase sum by at most the number of repeated tuples. -/
theorem norm_injective_sub_sum_pow_le (w : ι → Complex)
    (hw : ∀ x, ‖w x‖ = 1) (r : Nat) :
    ‖injectiveTupleTransform w r - (∑ x, w x) ^ r‖ ≤
      (((Fintype.card ι) ^ r - (Fintype.card ι).descFactorial r : Nat) : Real) := by
  rw [← allTupleTransform_eq_sum_pow]
  have hsplit := allTupleTransform_eq_injective_add_repeated w r
  rw [hsplit]
  convert norm_repeatedTupleTransform_le w hw r using 1
  rw [sub_add_cancel_left, norm_neg]

/-- Quantitative consequence for the ordinary phase sum.  A pointwise injective-transform bound
combined only with sampling without replacement controls the `r`th power of the ordinary period,
with the full repeated-tuple count as additive error. -/
theorem sum_norm_pow_le_of_injective_norm_le (w : ι → Complex)
    (hw : ∀ x, ‖w x‖ = 1) (r : Nat) (B : Real)
    (hB : ‖injectiveTupleTransform w r‖ ≤ B) :
    ‖∑ x, w x‖ ^ r ≤
      B + (((Fintype.card ι) ^ r - (Fintype.card ι).descFactorial r : Nat) : Real) := by
  have hdiff := norm_injective_sub_sum_pow_le w hw r
  calc
    ‖∑ x, w x‖ ^ r = ‖(∑ x, w x) ^ r‖ := by rw [norm_pow]
    _ = ‖((∑ x, w x) ^ r - injectiveTupleTransform w r) +
        injectiveTupleTransform w r‖ := by rw [sub_add_cancel]
    _ ≤ ‖(∑ x, w x) ^ r - injectiveTupleTransform w r‖ +
        ‖injectiveTupleTransform w r‖ := norm_add_le _ _
    _ = ‖injectiveTupleTransform w r - (∑ x, w x) ^ r‖ +
        ‖injectiveTupleTransform w r‖ := by rw [norm_sub_rev]
    _ ≤ (((Fintype.card ι) ^ r - (Fintype.card ι).descFactorial r : Nat) : Real) + B :=
      add_le_add hdiff hB
    _ = B + (((Fintype.card ι) ^ r - (Fintype.card ι).descFactorial r : Nat) : Real) :=
      add_comm _ _

/-- Constant aligned phases attain the combinatorial ceiling. -/
theorem injectiveTupleTransform_const (z : Complex) (r : Nat) :
    injectiveTupleTransform (fun _ : ι => z) r =
      ((Fintype.card ι).descFactorial r : Complex) * z ^ r := by
  classical
  unfold injectiveTupleTransform tupleMonomial
  rw [show (∑ f ∈ injectiveTuples r, ∏ i, z) =
      ∑ _f ∈ injectiveTuples r, z ^ r by
    apply Finset.sum_congr rfl
    intro f hf
    simp]
  rw [Finset.sum_const, nsmul_eq_mul, card_injectiveTuples]

/-- The coupling envelope is attained by the aligned unit phase `w=1`. -/
theorem norm_injective_sub_sum_pow_const_one (r : Nat) :
    ‖injectiveTupleTransform (fun _ : ι => (1 : Complex)) r -
        (∑ _x : ι, (1 : Complex)) ^ r‖ =
      (((Fintype.card ι) ^ r - (Fintype.card ι).descFactorial r : Nat) : Real) := by
  rw [injectiveTupleTransform_const]
  simp only [one_pow, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_ofNat]
  rw [norm_sub_rev]
  have hle : (Fintype.card ι).descFactorial r ≤ (Fintype.card ι) ^ r :=
    Nat.descFactorial_le_pow _ _
  rw [← Nat.cast_pow, ← Nat.cast_sub hle, Complex.norm_natCast]

/-! ## Exact production no-go -/

def productionN : Nat := 2 ^ 30

def samplingError : Nat :=
  productionN ^ 7 - productionN.descFactorial 7

def pointwiseEnergyBudget : Nat := 126871 * productionN ^ 7

/-- Integer ceiling for the square root of the per-frequency average energy budget. -/
def pointwiseAmplitudeCeiling : Nat := 14448764953860199458063090551701551

/-- Seventh-root ceiling produced by the generic coupling argument. -/
def samplingPeriodCeiling : Nat := 85047155

/-- Integer ceiling for the Paley scale `sqrt(2*n)`. -/
def paleyPeriodCeiling : Nat := 46341

/-- The generic sampling correction is a `185`-bit amplitude. -/
theorem samplingError_bitBounds :
    2 ^ 184 < samplingError ∧ samplingError < 2 ^ 185 := by
  norm_num [samplingError, productionN, Nat.descFactorial]

/-- The desired coefficient-`126871` per-frequency square budget is `227` bits. -/
theorem pointwiseEnergyBudget_bitBounds :
    2 ^ 226 < pointwiseEnergyBudget ∧ pointwiseEnergyBudget < 2 ^ 227 := by
  norm_num [pointwiseEnergyBudget, productionN]

/-- The square of the coupling error misses the pointwise energy scale by more than `2^141`. -/
theorem samplingError_sq_exceeds_budget_by_141_bits :
    2 ^ 141 * pointwiseEnergyBudget < samplingError ^ 2 := by
  norm_num [pointwiseEnergyBudget, samplingError, productionN, Nat.descFactorial]

/-- Aligned phases violate the desired coefficient-`126871` pointwise scale by over `2^192`.
This is the sharp falsifier for any phase-only exterior/Maclaurin inequality. -/
theorem aligned_injective_sq_exceeds_budget_by_192_bits :
    2 ^ 192 * pointwiseEnergyBudget <
      (productionN.descFactorial 7) ^ 2 := by
  norm_num [pointwiseEnergyBudget, productionN, Nat.descFactorial]

/-- The amplitude ceiling really covers the coefficient-`126871` square budget. -/
theorem pointwiseAmplitudeCeiling_sq_covers :
    pointwiseEnergyBudget ≤ pointwiseAmplitudeCeiling ^ 2 := by
  norm_num [pointwiseEnergyBudget, pointwiseAmplitudeCeiling, productionN]

/-- Exact seventh-root certificate for the coupling-derived period bound. -/
theorem samplingPeriodCeiling_certificate :
    pointwiseAmplitudeCeiling + samplingError ≤ samplingPeriodCeiling ^ 7 := by
  norm_num [pointwiseAmplitudeCeiling, samplingError, samplingPeriodCeiling,
    productionN, Nat.descFactorial]

/-- **The generic coupling yields only a very weak period bound.**  Even granting the full
coefficient-`126871` per-frequency square estimate for the injective transform, the universal
without-replacement comparison proves only `|sum w| ≤ 85,047,155`.  No subgroup hypothesis is
used here; improving this to Paley scale is exactly where subgroup mixing must enter. -/
theorem production_pointwise_injective_bound_implies_weak_period_bound
    (w : ι → Complex) (hw : ∀ x, ‖w x‖ = 1)
    (hcard : Fintype.card ι = productionN)
    (hD : ‖injectiveTupleTransform w 7‖ ^ 2 ≤ pointwiseEnergyBudget) :
    ‖∑ x, w x‖ ≤ samplingPeriodCeiling := by
  have hD' : ‖injectiveTupleTransform w 7‖ ≤ (pointwiseAmplitudeCeiling : Real) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : Nat) ≠ 0) (by positivity)
    exact hD.trans (by exact_mod_cast pointwiseAmplitudeCeiling_sq_covers)
  have hpow := sum_norm_pow_le_of_injective_norm_le w hw 7
    (pointwiseAmplitudeCeiling : Real) hD'
  rw [hcard] at hpow
  apply le_of_pow_le_pow_left₀ (by norm_num : (7 : Nat) ≠ 0) (by positivity)
  exact hpow.trans (by exact_mod_cast samplingPeriodCeiling_certificate)

/-- The coupling-derived ceiling is between `1835` and `1836` times the Paley ceiling. -/
theorem samplingPeriodCeiling_vs_paley :
    1835 * paleyPeriodCeiling < samplingPeriodCeiling ∧
      samplingPeriodCeiling < 1836 * paleyPeriodCeiling := by
  norm_num [paleyPeriodCeiling, samplingPeriodCeiling]

#print axioms allTupleTransform_eq_injective_add_repeated
#print axioms allTupleTransform_eq_sum_pow
#print axioms card_injectiveTuples
#print axioms card_repeatedTuples
#print axioms norm_injective_sub_sum_pow_le
#print axioms sum_norm_pow_le_of_injective_norm_le
#print axioms injectiveTupleTransform_const
#print axioms norm_injective_sub_sum_pow_const_one
#print axioms samplingError_bitBounds
#print axioms samplingError_sq_exceeds_budget_by_141_bits
#print axioms aligned_injective_sq_exceeds_budget_by_192_bits
#print axioms production_pointwise_injective_bound_implies_weak_period_bound
#print axioms samplingPeriodCeiling_vs_paley

end ArkLib.ProximityGap.Frontier.BGKSamplingWithoutReplacementNoGo
