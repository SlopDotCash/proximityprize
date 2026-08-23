/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ShortPhaseRbrKnowledgeLeaves

/-!
# The tight RLC kernel bound (issue #329, brick B1)

The `linearCombination` round of the composed Spartan PIOP samples a uniform
`r : R1CS.MatrixIdx → R` and forms the random linear combination `∑ idx, r idx * claim idx`.
A doomed prover whose claimed evaluations differ from the true ones by `d ≠ 0` survives the
round exactly when the sampled `r` lies in the kernel of the linear form `r ↦ ∑ idx, r idx * d idx`.

This file proves the **exact** kernel count and the resulting **exact** flip probability:

* `card_linearForm_kernel`: the kernel of a nonzero linear form on `R1CS.MatrixIdx → R`
  (a 3-dimensional space) has exactly `|R|²` elements;
* `probEvent_linearForm_kernel` / `probEvent_linearForm_kernel_coe`: the uniform-challenge
  kernel event has probability **exactly** `1 / |R|`, in the
  `Pr[fun r => _ | $ᵗ (R1CS.MatrixIdx → R)]` form consumed by
  `Verifier.rbrKnowledgeSoundness_singleChallenge_pure`;
* `probEvent_linearForm_kernel_le`: the `≤` form with the `ℝ≥0`-coerced error
  `(1 : ℝ≥0) / (Fintype.card R : ℝ≥0)` matching the per-round error shape of the existing
  leaves (`fun _ => (1 : ℝ≥0) / (Fintype.card R : ℝ≥0)`);
* `probEvent_linearForm_eq` / `probEvent_linearForm_eq_le`: the affine corollary
  `Pr[fun r => ∑ idx, r idx * a idx = ∑ idx, r idx * b idx] = 1 / |R|` for `a ≠ b`.

The exact equality doubles as the tightness certificate for hypothesis A3 of the `WithClaim`
line: no per-round error below `1 / |R|` is achievable at this round, since a prover whose
claim error is a *fixed* nonzero `d` is caught with probability exactly `1 - 1/|R|`.

The counting core (`card_linearForm_kernel_of_ne`) is generic over any finite index type and
any finite integral domain: the restriction map off a coordinate `i₀` with `d i₀ ≠ 0` is a
bijection from the kernel onto the functions on the remaining coordinates, because
multiplication by `d i₀` is injective (domain) and hence bijective (finiteness) — no field
structure or division is ever used.
-/

open OracleComp OracleSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

/-! ## Generic kernel counting over a finite integral domain -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {R : Type*} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
/-- **The kernel restriction bijection.** For a linear form `r ↦ ∑ i, r i * d i` with
`d i₀ ≠ 0`, restricting a kernel element to the coordinates `≠ i₀` is a bijection onto all
functions on those coordinates: the value at `i₀` is uniquely determined (injectivity of
multiplication by `d i₀` in a domain) and always recoverable (surjectivity of that
multiplication by finiteness). -/
theorem bijective_linearFormKernelRestrict (d : ι → R) (i₀ : ι) (hd : d i₀ ≠ 0) :
    Function.Bijective
      (fun (r : {r : ι → R // ∑ i, r i * d i = 0}) (j : {i : ι // i ≠ i₀}) => r.1 j.1) := by
  constructor
  · rintro ⟨r, hr⟩ ⟨s, hs⟩ h
    have h' : ∀ j : {i : ι // i ≠ i₀}, r j.1 = s j.1 := fun j => congrFun h j
    have htail : ∑ j : {i : ι // i ≠ i₀}, r j.1 * d j.1
        = ∑ j : {i : ι // i ≠ i₀}, s j.1 * d j.1 :=
      Finset.sum_congr rfl fun j _ => by rw [h' j]
    have hr' : r i₀ * d i₀ + ∑ j : {i : ι // i ≠ i₀}, r j.1 * d j.1 = 0 :=
      (Fintype.sum_eq_add_sum_subtype_ne (fun i => r i * d i) i₀).symm.trans hr
    have hs' : s i₀ * d i₀ + ∑ j : {i : ι // i ≠ i₀}, s j.1 * d j.1 = 0 :=
      (Fintype.sum_eq_add_sum_subtype_ne (fun i => s i * d i) i₀).symm.trans hs
    have hhead : r i₀ * d i₀ = s i₀ * d i₀ := by
      have h1 := eq_neg_of_add_eq_zero_left hr'
      have h2 := eq_neg_of_add_eq_zero_left hs'
      rw [h1, h2, htail]
    have hi₀ : r i₀ = s i₀ := mul_right_cancel₀ hd hhead
    exact Subtype.ext (funext fun i => by
      by_cases hi : i = i₀
      · subst hi; exact hi₀
      · exact h' ⟨i, hi⟩)
  · intro g
    -- Multiplication by `d i₀` is injective in a domain, hence bijective by finiteness.
    have hmul : Function.Bijective (fun x : R => x * d i₀) :=
      Finite.injective_iff_bijective.mp fun a b hab => mul_right_cancel₀ hd hab
    obtain ⟨x, hx⟩ := hmul.2 (-(∑ j : {i : ι // i ≠ i₀}, g j * d j.1))
    have hx' : x * d i₀ = -(∑ j : {i : ι // i ≠ i₀}, g j * d j.1) := hx
    refine ⟨⟨fun i => if h : i = i₀ then x else g ⟨i, h⟩, ?_⟩, ?_⟩
    · calc ∑ i, (if h : i = i₀ then x else g ⟨i, h⟩) * d i
          = (if h : i₀ = i₀ then x else g ⟨i₀, h⟩) * d i₀
            + ∑ j : {i : ι // i ≠ i₀}, (if h : j.1 = i₀ then x else g ⟨j.1, h⟩) * d j.1 :=
            Fintype.sum_eq_add_sum_subtype_ne _ i₀
        _ = x * d i₀ + ∑ j : {i : ι // i ≠ i₀}, g j * d j.1 := by
            rw [dif_pos rfl]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by rw [dif_neg j.2]
        _ = 0 := by rw [hx']; exact neg_add_cancel _
    · funext j
      show (if h : j.1 = i₀ then x else g ⟨j.1, h⟩) = g j
      rw [dif_neg j.2]

/-- **Generic kernel count.** The kernel of a linear form with a nonzero coefficient at `i₀`
has exactly `|R| ^ (|ι| - 1)` elements. -/
theorem card_linearForm_kernel_of_ne (d : ι → R) (i₀ : ι) (hd : d i₀ ≠ 0) :
    Fintype.card {r : ι → R // ∑ i, r i * d i = 0}
      = Fintype.card R ^ (Fintype.card ι - 1) := by
  rw [Fintype.card_of_bijective (bijective_linearFormKernelRestrict d i₀ hd),
    Fintype.card_fun]
  congr 1
  have hcard : Fintype.card {i : ι // i ≠ i₀} + 1 = Fintype.card ι := by
    rw [← Fintype.card_option]
    exact Fintype.card_congr (Equiv.optionSubtypeNe i₀)
  omega

end Generic

/-! ## The `R1CS.MatrixIdx` specialization -/

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]

/-- `R1CS.MatrixIdx` has exactly three elements (`A`, `B`, `C`). -/
@[simp]
theorem card_matrixIdx : Fintype.card R1CS.MatrixIdx = 3 := rfl

/-- **The RLC kernel count (subtype form).** For a nonzero claim-error vector
`d : R1CS.MatrixIdx → R`, exactly `|R|²` of the `|R|³` RLC challenges annihilate it. -/
theorem card_linearForm_kernel (d : R1CS.MatrixIdx → R) (hd : d ≠ 0) :
    Fintype.card {r : R1CS.MatrixIdx → R // ∑ idx, r idx * d idx = 0}
      = Fintype.card R ^ 2 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hd
  have hi₀' : d i₀ ≠ 0 := by simpa using hi₀
  rw [card_linearForm_kernel_of_ne d i₀ hi₀', card_matrixIdx]

/-- **The RLC kernel count (filter form),** phrased so it rewrites directly under
`probEvent_uniformSample`. -/
theorem card_filter_linearForm_kernel (d : R1CS.MatrixIdx → R) (hd : d ≠ 0) :
    (Finset.univ.filter
        (fun r : R1CS.MatrixIdx → R => ∑ idx, r idx * d idx = 0)).card
      = Fintype.card R ^ 2 := by
  rw [← Fintype.card_subtype]
  exact card_linearForm_kernel d hd

section Probability

variable [SampleableType (R1CS.MatrixIdx → R)]

/-- **The exact RLC kernel flip probability.** A uniformly sampled RLC challenge annihilates a
fixed nonzero claim-error vector `d` with probability exactly `1 / |R|`. Stated in the
`Pr[_ | $ᵗ C]` form consumed by `Verifier.rbrKnowledgeSoundness_singleChallenge_pure`
(`C := LinearCombinationChallenge R = R1CS.MatrixIdx → R`). -/
theorem probEvent_linearForm_kernel (d : R1CS.MatrixIdx → R) (hd : d ≠ 0) :
    Pr[fun r : R1CS.MatrixIdx → R => (∑ idx, r idx * d idx) = 0
      | $ᵗ (R1CS.MatrixIdx → R)]
      = 1 / (Fintype.card R : ENNReal) := by
  classical
  rw [probEvent_uniformSample, card_filter_linearForm_kernel d hd, Fintype.card_fun,
    card_matrixIdx]
  have hq0 : ((Fintype.card R : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  rw [Nat.cast_pow, Nat.cast_pow]
  calc ((Fintype.card R : ENNReal) ^ 2) / ((Fintype.card R : ENNReal) ^ 3)
      = ((Fintype.card R : ENNReal) ^ 2 * 1)
        / ((Fintype.card R : ENNReal) ^ 2 * (Fintype.card R : ENNReal)) := by
        rw [mul_one]; congr 1
    _ = 1 / (Fintype.card R : ENNReal) :=
        ENNReal.mul_div_mul_left 1 _ (pow_ne_zero 2 hq0)
          (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

/-- The exact RLC kernel flip probability, with the bound written as the `ℝ≥0`-coercion
`(1 : ℝ≥0) / (Fintype.card R : ℝ≥0)` — the exact error shape of the short-phase leaves. This
is the tightness certificate for hypothesis A3: the flip probability is *equal* to, not merely
bounded by, the claimed per-round error. -/
theorem probEvent_linearForm_kernel_coe (d : R1CS.MatrixIdx → R) (hd : d ≠ 0) :
    Pr[fun r : R1CS.MatrixIdx → R => (∑ idx, r idx * d idx) = 0
      | $ᵗ (R1CS.MatrixIdx → R)]
      = (((1 : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0) : ENNReal) := by
  rw [probEvent_linearForm_kernel d hd,
    ENNReal.coe_div (by exact_mod_cast Fintype.card_pos.ne' :
      ((Fintype.card R : ℝ≥0)) ≠ 0)]
  simp

/-- **The `≤` form of the RLC kernel flip bound,** ready for the `hflip` hypothesis of
`Verifier.rbrKnowledgeSoundness_singleChallenge_pure` with per-round error
`fun _ => (1 : ℝ≥0) / (Fintype.card R : ℝ≥0)`. -/
theorem probEvent_linearForm_kernel_le (d : R1CS.MatrixIdx → R) (hd : d ≠ 0) :
    Pr[fun r : R1CS.MatrixIdx → R => (∑ idx, r idx * d idx) = 0
      | $ᵗ (R1CS.MatrixIdx → R)]
      ≤ (((1 : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0) : ENNReal) :=
  le_of_eq (probEvent_linearForm_kernel_coe d hd)

/-- **The affine corollary.** If the claimed evaluations `a` differ from the true ones `b`,
a uniform RLC challenge produces matching combined claims with probability exactly `1 / |R|`. -/
theorem probEvent_linearForm_eq (a b : R1CS.MatrixIdx → R) (hab : a ≠ b) :
    Pr[fun r : R1CS.MatrixIdx → R =>
        (∑ idx, r idx * a idx) = (∑ idx, r idx * b idx)
      | $ᵗ (R1CS.MatrixIdx → R)]
      = 1 / (Fintype.card R : ENNReal) := by
  have hsum : ∀ r : R1CS.MatrixIdx → R,
      ∑ idx, r idx * (a - b) idx
        = (∑ idx, r idx * a idx) - (∑ idx, r idx * b idx) := by
    intro r
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, mul_sub]
  have hfun : (fun r : R1CS.MatrixIdx → R =>
        (∑ idx, r idx * a idx) = (∑ idx, r idx * b idx))
      = (fun r : R1CS.MatrixIdx → R => (∑ idx, r idx * (a - b) idx) = 0) := by
    funext r
    apply propext
    rw [hsum r, sub_eq_zero]
  rw [hfun]
  exact probEvent_linearForm_kernel (a - b) (sub_ne_zero.mpr hab)

/-- The affine corollary in `≤` form with the `ℝ≥0`-coerced leaf error. -/
theorem probEvent_linearForm_eq_le (a b : R1CS.MatrixIdx → R) (hab : a ≠ b) :
    Pr[fun r : R1CS.MatrixIdx → R =>
        (∑ idx, r idx * a idx) = (∑ idx, r idx * b idx)
      | $ᵗ (R1CS.MatrixIdx → R)]
      ≤ (((1 : ℝ≥0) / (Fintype.card R : ℝ≥0) : ℝ≥0) : ENNReal) := by
  rw [probEvent_linearForm_eq a b hab,
    ENNReal.coe_div (by exact_mod_cast Fintype.card_pos.ne' :
      ((Fintype.card R : ℝ≥0)) ≠ 0)]
  simp

end Probability

end Spartan.Spec.Bricks

#print axioms Spartan.Spec.Bricks.bijective_linearFormKernelRestrict
#print axioms Spartan.Spec.Bricks.card_linearForm_kernel_of_ne
#print axioms Spartan.Spec.Bricks.card_matrixIdx
#print axioms Spartan.Spec.Bricks.card_linearForm_kernel
#print axioms Spartan.Spec.Bricks.card_filter_linearForm_kernel
#print axioms Spartan.Spec.Bricks.probEvent_linearForm_kernel
#print axioms Spartan.Spec.Bricks.probEvent_linearForm_kernel_coe
#print axioms Spartan.Spec.Bricks.probEvent_linearForm_kernel_le
#print axioms Spartan.Spec.Bricks.probEvent_linearForm_eq
#print axioms Spartan.Spec.Bricks.probEvent_linearForm_eq_le
