/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.PrimitiveElement
set_option linter.style.longLine false

/-!
# Norm bound for sums of roots of unity (#407 — the deep-moment anomaly fragment)

The provable kernel behind `A_r = 0 for (2r)^{n/2} < p`: a nonzero algebraic integer that is a sum of
few roots of unity has small norm, hence cannot be divisible by a large rational prime.

> **`abs_norm_sum_rootsOfUnity_le`** — for `α = Σ_{i∈s} u_i` with each `u_i` a root of unity in a number
> field `K`, `|N_{K/ℚ}(α)| ≤ (#s)^{[K:ℚ]}`.

Corollary (`prime_not_dvd_norm_sum_rootsOfUnity`): if `p` is a rational prime with `p > (#s)^{[K:ℚ]}`
then `p ∤ N(α)` unless `N(α)=0` — so over `ℚ(ζ_n)` (`[K:ℚ]=φ(n)`) a nonzero sum of `≤ m` roots of unity
is never `≡ 0 mod 𝔭` once `m^{φ(n)} < p`. Axiom-clean.
-/

open Finset NumberField Module

namespace ArkLib.ProximityGap.RootSumNorm

variable {K : Type*} [Field K] [NumberField K]

/-- The house (largest conjugate modulus) of a root of unity is `≤ 1`. -/
theorem house_rootOfUnity_le_one {u : K} {k : ℕ} (hk : k ≠ 0) (hu : u ^ k = 1) :
    house u ≤ 1 := by
  rw [house_eq_sup', ← NNReal.coe_one, NNReal.coe_le_coe]
  refine Finset.sup'_le _ _ (fun σ _ => ?_)
  rw [Complex.nnnorm_eq_one_of_pow_eq_one (by rw [← map_pow, hu, map_one]) hk]

/-- `|N_{K/ℚ}(α)| ≤ house(α)^{[K:ℚ]}`. -/
theorem abs_norm_le_house_pow (α : K) :
    ((|Algebra.norm ℚ α| : ℚ) : ℝ) ≤ house α ^ finrank ℚ K := by
  have key : (algebraMap ℚ ℂ) (Algebra.norm ℚ α) = ∏ σ : K →ₐ[ℚ] ℂ, σ α :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ α
  have hnorm : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ α)‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
    simp [eq_ratCast, Complex.norm_ratCast, Rat.cast_abs]
  calc ((|Algebra.norm ℚ α| : ℚ) : ℝ)
      = ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ α)‖ := hnorm.symm
    _ = ‖∏ σ : K →ₐ[ℚ] ℂ, σ α‖ := by rw [key]
    _ = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ α‖ := by rw [norm_prod]
    _ ≤ ∏ _σ : K →ₐ[ℚ] ℂ, house α :=
        Finset.prod_le_prod (fun σ _ => norm_nonneg _)
          (fun σ _ => norm_embedding_le_house α σ.toRingHom)
    _ = house α ^ (Fintype.card (K →ₐ[ℚ] ℂ)) := by rw [Finset.prod_const, Finset.card_univ]
    _ = house α ^ finrank ℚ K := by
        rw [AlgHom.card_of_splits ℚ K ℂ (fun _ ↦ IsAlgClosed.splits _)]

/-- **The norm of a sum of roots of unity is bounded by `(#terms)^{[K:ℚ]}`.** -/
theorem abs_norm_sum_rootsOfUnity_le {ι : Type*} (s : Finset ι) (u : ι → K)
    (k : ι → ℕ) (hk : ∀ i ∈ s, k i ≠ 0) (hu : ∀ i ∈ s, u i ^ (k i) = 1) :
    ((|Algebra.norm ℚ (∑ i ∈ s, u i)| : ℚ) : ℝ) ≤ (s.card : ℝ) ^ finrank ℚ K := by
  refine (abs_norm_le_house_pow _).trans ?_
  apply pow_le_pow_left₀ (house_nonneg _)
  calc house (∑ i ∈ s, u i)
      ≤ ∑ i ∈ s, house (u i) := house_sum_le_sum_house s u
    _ ≤ ∑ _i ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => house_rootOfUnity_le_one (hk i hi) (hu i hi))
    _ = (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Large primes do not divide the norm of a nonzero sum of roots of unity.** If `α = Σ_{i∈s} u_i`
(roots of unity) has `N(α) ≠ 0` and `p` is a natural number with `(#s)^{[K:ℚ]} < p`, then
`(p : ℤ) ∤ ` the integer `N(α)` is forced via the bound (here phrased as the strict size inequality
`|N(α)| < p`, which precludes `p ∣ N(α)` for nonzero `N`). -/
theorem abs_norm_lt_of_card_pow_lt {ι : Type*} (s : Finset ι) (u : ι → K)
    (k : ι → ℕ) (hk : ∀ i ∈ s, k i ≠ 0) (hu : ∀ i ∈ s, u i ^ (k i) = 1)
    {p : ℕ} (hp : (s.card : ℝ) ^ finrank ℚ K < p) :
    ((|Algebra.norm ℚ (∑ i ∈ s, u i)| : ℚ) : ℝ) < p :=
  lt_of_le_of_lt (abs_norm_sum_rootsOfUnity_le s u k hk hu) hp

/-- A nonzero integer whose absolute value is smaller than `p` is not divisible by `p`. -/
theorem int_not_dvd_of_natAbs_lt {N : ℤ} {p : ℕ} (hN0 : N ≠ 0) (hlt : N.natAbs < p) :
    ¬ (p : ℤ) ∣ N := by
  intro hdvd
  have hpdvd : p ∣ N.natAbs := by
    exact_mod_cast (Int.dvd_natAbs.mpr hdvd)
  have hNpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN0
  exact (Nat.not_le.mpr hlt) (Nat.le_of_dvd hNpos hpdvd)

/-- **Integer norm non-divisibility corollary.**  Suppose the rational norm of the root-of-unity
sum is represented by an integer `N`.  If `(#s)^[K:ℚ] < p` and `N ≠ 0`, then `p` does not divide
that integer norm.  This is the executable form of the clean-range transfer used by the #407
char-`p` anomaly analysis. -/
theorem prime_not_dvd_int_norm_sum_rootsOfUnity {ι : Type*} (s : Finset ι) (u : ι → K)
    (k : ι → ℕ) (hk : ∀ i ∈ s, k i ≠ 0) (hu : ∀ i ∈ s, u i ^ (k i) = 1)
    {p : ℕ} {N : ℤ} (hN : (N : ℚ) = Algebra.norm ℚ (∑ i ∈ s, u i)) (hN0 : N ≠ 0)
    (hp : (s.card : ℝ) ^ finrank ℚ K < p) :
    ¬ (p : ℤ) ∣ N := by
  have hlt_rat :
      ((|Algebra.norm ℚ (∑ i ∈ s, u i)| : ℚ) : ℝ) < p :=
    abs_norm_lt_of_card_pow_lt s u k hk hu hp
  have hlt_int : (N.natAbs : ℝ) < p := by
    have habs : |Algebra.norm ℚ (∑ i ∈ s, u i)| = (N.natAbs : ℚ) := by
      rw [← hN]
      simp
    simpa [habs] using hlt_rat
  exact int_not_dvd_of_natAbs_lt hN0 (by exact_mod_cast hlt_int)

end ArkLib.ProximityGap.RootSumNorm

#print axioms ArkLib.ProximityGap.RootSumNorm.abs_norm_sum_rootsOfUnity_le
#print axioms ArkLib.ProximityGap.RootSumNorm.abs_norm_lt_of_card_pow_lt
#print axioms ArkLib.ProximityGap.RootSumNorm.int_not_dvd_of_natAbs_lt
#print axioms ArkLib.ProximityGap.RootSumNorm.prime_not_dvd_int_norm_sum_rootsOfUnity
