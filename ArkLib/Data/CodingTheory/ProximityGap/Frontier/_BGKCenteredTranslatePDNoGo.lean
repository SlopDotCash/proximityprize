/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Positive-definite centered-translate no-go for the depth-seven residual

This file isolates a limitation of a tempting centered-translate route.  Suppose a real kernel
`D` on an additive finite group is known only to

* have global mean zero;
* be additive positive semidefinite;
* be invariant under multiplication by a chosen set `G`.

Those three homogeneous properties cannot, by themselves, upper-bound the signed restriction
`sum_(u in G) D(1-u)`: a five-point centered delta kernel satisfies all three properties and has
positive restriction, so its nonnegative scaling ray defeats every fixed upper bound.

The final section pins the exact proper-subgroup computation at `p = 13313`, `n = 256`.  For the
centered autocorrelation of the ordered six-fold representation function, the normalized
depth-seven defect is

`584598921140164042747377 / 1873638182474481664 = 312012.706... > 2^18`.

The deterministic integer computation and all structural checks are in
`scripts/probes/probe_bgk_ctr_pd_no_go.py`; the theorems here certify the abstract obstruction and
the exact rational arithmetic.  No analytic estimate is claimed.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKCenteredTranslatePDNoGo

/-! ## The three structural hypotheses -/

/-- Additive positive semidefiniteness of a translation kernel. -/
def AdditivePositiveSemidefinite {A : Type*} [Fintype A] [AddGroup A]
    (D : A → ℝ) : Prop :=
  ∀ c : A → ℝ, 0 ≤ ∑ x, ∑ y, c x * c y * D (x - y)

/-- Global mean-zero condition. -/
def GlobalMeanZero {A : Type*} [Fintype A] (D : A → ℝ) : Prop :=
  ∑ x, D x = 0

/-- Invariance under multiplication by every element of `G`. -/
def MultiplicativelyInvariant {A : Type*} [Fintype A] [Mul A]
    (G : Finset A) (D : A → ℝ) : Prop :=
  ∀ g ∈ G, ∀ x, D (g * x) = D x

/-- The centered-translate objective occurring in the depth-seven energy identity. -/
def signedRestriction {A : Type*} [Fintype A] [Sub A] [One A]
    (G : Finset A) (D : A → ℝ) : ℝ :=
  ∑ u ∈ G, D (1 - u)

/-! ## A finite Fourier-nonnegative witness -/

section CenteredDelta

variable {A : Type*} [Fintype A] [DecidableEq A] [AddGroup A]

/-- The centered delta kernel `|A| 1_{x=0} - 1`.

Its additive Fourier weights are zero at the trivial character and one common nonnegative weight
at every nontrivial character.  The proof below uses the equivalent quadratic-form criterion and
finite Cauchy--Schwarz, avoiding any character API. -/
def centeredDeltaKernel (x : A) : ℝ :=
  if x = 0 then (Fintype.card A : ℝ) - 1 else -1

lemma centeredDeltaKernel_eq_indicator (x : A) :
    centeredDeltaKernel x =
      (Fintype.card A : ℝ) * (if x = 0 then 1 else 0) - 1 := by
  by_cases hx : x = 0 <;> simp [centeredDeltaKernel, hx]

/-- The centered delta kernel has exactly zero global mean. -/
theorem centeredDeltaKernel_globalMeanZero :
    GlobalMeanZero (centeredDeltaKernel : A → ℝ) := by
  classical
  simp [GlobalMeanZero, centeredDeltaKernel_eq_indicator]

/-- Exact quadratic form of the centered delta kernel. -/
lemma centeredDeltaKernel_quadraticForm (c : A → ℝ) :
    (∑ x, ∑ y, c x * c y * centeredDeltaKernel (x - y)) =
      (Fintype.card A : ℝ) * ∑ x, (c x) ^ 2 - (∑ x, c x) ^ 2 := by
  classical
  have hpoint (x y : A) :
      c x * c y * centeredDeltaKernel (x - y) =
        (Fintype.card A : ℝ) * (if y = x then (c x) ^ 2 else 0) - c x * c y := by
    rw [centeredDeltaKernel_eq_indicator]
    by_cases hxy : y = x
    · subst y
      simp
      ring
    · have hsub : x - y ≠ 0 := by simpa [sub_eq_zero] using Ne.symm hxy
      simp [hxy, hsub]
  simp_rw [hpoint, Finset.sum_sub_distrib, mul_ite]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero]
  rw [show (∑ x, ∑ y, c x * c y) = (∑ x, c x) ^ 2 by
    calc
      (∑ x, ∑ y, c x * c y) = ∑ x, c x * ∑ y, c y := by
        congr 1
        funext x
        exact (Finset.mul_sum (s := Finset.univ) (f := c) (a := c x)).symm
      _ = (∑ x, c x) * ∑ y, c y := by
        exact (Finset.sum_mul (s := Finset.univ) (f := c) (a := ∑ y, c y)).symm
      _ = (∑ x, c x) ^ 2 := by ring]
  rw [← Finset.mul_sum]

/-- The centered delta kernel is additive positive semidefinite. -/
theorem centeredDeltaKernel_additivePositiveSemidefinite :
    AdditivePositiveSemidefinite (centeredDeltaKernel : A → ℝ) := by
  intro c
  rw [centeredDeltaKernel_quadraticForm]
  have hcs :
      (∑ x, c x) ^ 2 ≤ (Fintype.card A : ℝ) * ∑ x, (c x) ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset A)) (f := c))
  linarith

end CenteredDelta

/-! ## A five-point orbit-invariant counterexample and its scaling ray -/

abbrev Five := ZMod 5

/-- The proper multiplicative subgroup `{1,-1}` in `F_5^*`. -/
def signSubgroup : Finset Five := {1, -1}

lemma five_neg_one_ne_one : (-1 : Five) ≠ 1 := by
  intro h
  have hval := congrArg ZMod.val h
  change 4 = 1 at hval
  omega

lemma five_one_ne_neg_one : (1 : Five) ≠ -1 := Ne.symm five_neg_one_ne_one

lemma five_two_ne_zero : (1 : Five) + 1 ≠ 0 := by
  intro h
  have hval := congrArg ZMod.val h
  change 2 = 0 at hval
  omega

theorem signSubgroup_card : signSubgroup.card = 2 := by
  change ({1, -1} : Finset Five).card = 2
  rw [Finset.card_insert_of_notMem]
  · simp
  · simpa using five_one_ne_neg_one

theorem five_centeredDelta_invariant :
    MultiplicativelyInvariant signSubgroup (centeredDeltaKernel : Five → ℝ) := by
  intro g hg x
  simp only [signSubgroup, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl
  · simp
  · simp [centeredDeltaKernel]

/-- The restriction is strictly positive: `D(0) + D(2) = 4 - 1 = 3`. -/
theorem five_centeredDelta_signedRestriction :
    signedRestriction signSubgroup (centeredDeltaKernel : Five → ℝ) = 3 := by
  simp [signedRestriction, signSubgroup, centeredDeltaKernel, five_one_ne_neg_one,
    five_two_ne_zero]
  norm_num

lemma globalMeanZero_nonnegScale {A : Type*} [Fintype A]
    {D : A → ℝ} (hD : GlobalMeanZero D) (t : ℝ) :
    GlobalMeanZero (fun x => t * D x) := by
  simpa [GlobalMeanZero, Finset.mul_sum] using congrArg (fun z : ℝ => t * z) hD

lemma multiplicativelyInvariant_scale {A : Type*} [Fintype A] [Mul A]
    {G : Finset A} {D : A → ℝ} (hD : MultiplicativelyInvariant G D) (t : ℝ) :
    MultiplicativelyInvariant G (fun x => t * D x) := by
  intro g hg x
  change t * D (g * x) = t * D x
  rw [hD g hg x]

lemma additivePositiveSemidefinite_nonnegScale
    {A : Type*} [Fintype A] [AddGroup A] {D : A → ℝ}
    (hD : AdditivePositiveSemidefinite D) {t : ℝ} (ht : 0 ≤ t) :
    AdditivePositiveSemidefinite (fun x => t * D x) := by
  intro c
  have hbase := hD c
  have heq :
      (∑ x, ∑ y, c x * c y * (t * D (x - y))) =
        t * ∑ x, ∑ y, c x * c y * D (x - y) := by
    simp_rw [show ∀ x y : A,
        c x * c y * (t * D (x - y)) = t * (c x * c y * D (x - y)) by
      intro x y
      ring]
    rw [Finset.mul_sum]
    congr 1
    funext x
    rw [Finset.mul_sum]
  rw [heq]
  exact mul_nonneg ht hbase

lemma signedRestriction_scale {A : Type*} [Fintype A] [Sub A] [One A]
    (G : Finset A) (D : A → ℝ) (t : ℝ) :
    signedRestriction G (fun x => t * D x) = t * signedRestriction G D := by
  simp [signedRestriction, Finset.mul_sum]

/-- **Abstract no-go.**  Zero mean, additive PSD, and multiplicative invariance alone admit a
positive scaling ray whose centered-translate restriction exceeds every prescribed real bound. -/
theorem three_structural_properties_do_not_bound_restriction (B : ℝ) :
    ∃ D : Five → ℝ,
      GlobalMeanZero D ∧
      AdditivePositiveSemidefinite D ∧
      MultiplicativelyInvariant signSubgroup D ∧
      B < signedRestriction signSubgroup D := by
  let t : ℝ := |B| + 1
  let D : Five → ℝ := fun x => t * centeredDeltaKernel x
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · exact globalMeanZero_nonnegScale centeredDeltaKernel_globalMeanZero t
  · exact additivePositiveSemidefinite_nonnegScale
      centeredDeltaKernel_additivePositiveSemidefinite ht
  · exact multiplicativelyInvariant_scale five_centeredDelta_invariant t
  · rw [show D = fun x => t * centeredDeltaKernel x by rfl,
      signedRestriction_scale, five_centeredDelta_signedRestriction]
    dsimp [t]
    have hB : B ≤ |B| := le_abs_self B
    nlinarith

/-! ## Exact `p=13313`, `n=256` proper-subgroup certificate -/

/-- Ordered seven-fold additive energy from the exact probe. -/
def cellEnergySeven : ℕ := 390017062859571490445015114240

/-- `p E_7 - n^14`, equivalently `n * sum_(u in G) D(1-u)`. -/
def cellCenteredNumerator : ℕ := 299314647623763989886657024

/-- The natural `p n^7` normalizer. -/
def cellNormalizer : ℕ := 959302749426934611968

/-- Exact recomputation of the centered numerator from `p`, `n`, and `E_7`. -/
theorem cellCenteredNumerator_eq :
    cellCenteredNumerator = 13313 * cellEnergySeven - 256 ^ 14 := by
  norm_num [cellCenteredNumerator, cellEnergySeven]

/-- Exact translate identity using the restriction value emitted by the probe. -/
theorem cell_restriction_identity :
    256 * 1169197842280328085494754 = cellCenteredNumerator := by
  norm_num [cellCenteredNumerator]

/-- Exact natural-number normalizer identity `p n^7`. -/
theorem cellNormalizer_eq : cellNormalizer = 13313 * 256 ^ 7 := by
  norm_num [cellNormalizer]

/-- Reduced exact coefficient of the normalized centered depth-seven defect. -/
theorem cell_reduced_coefficient :
    (cellCenteredNumerator : ℚ) / cellNormalizer =
      584598921140164042747377 / 1873638182474481664 := by
  norm_num [cellCenteredNumerator, cellNormalizer]

/-- The proper-subgroup cell already exceeds coefficient `2^18` in the `p n^7` normalization. -/
theorem cell_exceeds_two_pow_eighteen :
    (2 ^ 18 : ℚ) < (cellCenteredNumerator : ℚ) / cellNormalizer := by
  norm_num [cellCenteredNumerator, cellNormalizer]

/-- Exact positive integer margin over the coefficient-`2^18` target. -/
theorem cell_positive_margin :
    cellCenteredNumerator - 2 ^ 18 * cellNormalizer =
      47839187677989642966917632 := by
  norm_num [cellCenteredNumerator, cellNormalizer]

#print axioms centeredDeltaKernel_globalMeanZero
#print axioms centeredDeltaKernel_additivePositiveSemidefinite
#print axioms three_structural_properties_do_not_bound_restriction
#print axioms cellCenteredNumerator_eq
#print axioms cell_reduced_coefficient
#print axioms cell_exceeds_two_pow_eighteen

end ArkLib.ProximityGap.Frontier.BGKCenteredTranslatePDNoGo
