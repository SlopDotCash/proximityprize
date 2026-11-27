/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PlaneBezoutWithMultiplicity
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Projective linear changes and linear-polar nonvanishing for plane curves -/

set_option autoImplicit false
noncomputable section

open Polynomial MvPolynomial Finset Module
open scoped Matrix
open ArkLib.ProximityGap.Frontier.PlaneBezoutWithMultiplicity

namespace ArkLib.ProximityGap.Frontier.PlaneCurveLinearAlgebra

section LinearChanges

variable {K : Type*} [Field K]

/-- Linear substitution of variables `(X 0, X 1, X 2)` by `M : Matrix (Fin 3) (Fin 3) K`. -/
def substLin (M : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval fun i => ∑ j : Fin 3, MvPolynomial.C (M i j) * MvPolynomial.X j

/-- Pullback of a dual polynomial `P` along the gradient `(∂₀ F, ∂₁ F, ∂₂ F)`. -/
def gaussPullback (F P : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval ![pderiv 0 F, pderiv 1 F, pderiv 2 F] P

theorem substLin_X (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    substLin M (MvPolynomial.X i) = ∑ j : Fin 3, MvPolynomial.C (M i j) * MvPolynomial.X j := by
  simp [substLin]

@[simp]
theorem substLin_C (M : Matrix (Fin 3) (Fin 3) K) (c : K) :
    substLin M (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [substLin]

theorem substLin_one : substLin (1 : Matrix (Fin 3) (Fin 3) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [substLin_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.one_apply_eq]
  · intro j _ hji; simp [Matrix.one_apply_ne (Ne.symm hji)]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem substLin_comp (M N : Matrix (Fin 3) (Fin 3) K) :
    (substLin M).comp (substLin N) = substLin (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, substLin_X, map_sum, map_mul, substLin_C]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]; ring

/-- An invertible matrix `M` (with inverse `N`) induces an algebra automorphism `substLinEquiv`. -/
def substLinEquiv (M N : Matrix (Fin 3) (Fin 3) K) (hMN : M * N = 1) (hNM : N * M = 1) :
    MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K :=
  AlgEquiv.ofAlgHom (substLin M) (substLin N)
    (by rw [substLin_comp, hNM, substLin_one])
    (by rw [substLin_comp, hMN, substLin_one])

theorem substLin_isHomogeneous (M : Matrix (Fin 3) (Fin 3) K) {F : MvPolynomial (Fin 3) K} {d : ℕ}
    (hF : F.IsHomogeneous d) : (substLin M F).IsHomogeneous d := by
  classical
  have hlin (i : Fin 3) : (substLin M (MvPolynomial.X i)).IsHomogeneous 1 := by
    rw [substLin_X, ← mem_homogeneousSubmodule]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mem_homogeneousSubmodule]
    simpa using (MvPolynomial.isHomogeneous_C (Fin 3) (M i j)).mul
      (MvPolynomial.isHomogeneous_X K j)
  have hpow (i : Fin 3) (k : ℕ) : (substLin M (MvPolynomial.X i) ^ k).IsHomogeneous k := by
    simpa [mul_one] using (hlin i).pow k
  rw [F.as_sum, map_sum, ← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_homogeneousSubmodule]
  have hdeg : m 0 + m 1 + m 2 = d := by
    have h := hF (MvPolynomial.mem_support_iff.mp hm)
    rwa [weight_one_eq_sum, m3_sum] at h
  have hmon : MvPolynomial.monomial m (F.coeff m) =
      MvPolynomial.C (F.coeff m) * MvPolynomial.X 0 ^ m 0 *
        MvPolynomial.X 1 ^ m 1 * MvPolynomial.X 2 ^ m 2 := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.X,
      MvPolynomial.monomial_pow, MvPolynomial.monomial_pow, MvPolynomial.monomial_pow,
      MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial,
      MvPolynomial.monomial_mul_monomial]
    simp only [one_pow, mul_one, Finsupp.smul_single, smul_eq_mul]
    exact congrArg (fun d => MvPolynomial.monomial d (F.coeff m)) (by ext i; fin_cases i <;> simp)
  rw [hmon, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, substLin_C]
  have h0 := (MvPolynomial.isHomogeneous_C (Fin 3) (F.coeff m)).mul (hpow 0 (m 0))
  have h1 := h0.mul (hpow 1 (m 1))
  have h2 := h1.mul (hpow 2 (m 2))
  rwa [zero_add, hdeg] at h2

/-- Chain rule for partial derivatives under a linear change of variables. -/
theorem pderiv_substLin (M : Matrix (Fin 3) (Fin 3) K) (j : Fin 3) (G : MvPolynomial (Fin 3) K) :
    pderiv j (substLin M G) = ∑ i : Fin 3, MvPolynomial.C (M i j) * substLin M (pderiv i G) := by
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    rw [map_mul, pderiv_mul, hp]
    simp_rw [pderiv_mul, map_add, map_mul, mul_add]
    have hXk : pderiv j (substLin M (MvPolynomial.X k)) = MvPolynomial.C (M k j) := by
      rw [substLin_X, map_sum]
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hlj
        rw [pderiv_C_mul, pderiv_X_of_ne hlj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hXk, Finset.sum_mul, Finset.sum_add_distrib]
    have hterm2 : ∑ i : Fin 3, MvPolynomial.C (M i j) *
        (substLin M p * substLin M (pderiv i (MvPolynomial.X k))) =
        substLin M p * MvPolynomial.C (M k j) := by
      rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro i _ hik
        rw [pderiv_X_of_ne (Ne.symm hik), map_zero, mul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hterm2]
    exact congrArg (· + substLin M p * MvPolynomial.C (M k j))
      (Finset.sum_congr rfl fun i _ => by ring)

/-- Covariance of `gaussPullback` under an invertible linear change of coordinates. -/
theorem gaussPullback_substLin (M N : Matrix (Fin 3) (Fin 3) K)
    (hMN : M * N = 1) (F P : MvPolynomial (Fin 3) K) :
    gaussPullback (substLin M F) (substLin Nᵀ P) = substLin M (gaussPullback F P) := by
  have hcomp :
      (MvPolynomial.aeval ![pderiv 0 (substLin M F), pderiv 1 (substLin M F),
          pderiv 2 (substLin M F)]).comp (substLin Nᵀ) =
      (substLin M).comp
        (MvPolynomial.aeval ![pderiv 0 F, pderiv 1 F, pderiv 2 F]) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, substLin_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, MvPolynomial.aeval_X, Matrix.transpose_apply]
    have hvec (j : Fin 3) : (![pderiv 0 (substLin M F), pderiv 1 (substLin M F),
        pderiv 2 (substLin M F)] : Fin 3 → MvPolynomial (Fin 3) K) j = pderiv j (substLin M F) := by
      fin_cases j <;> rfl
    have hvec' : (![pderiv 0 F, pderiv 1 F, pderiv 2 F] : Fin 3 → MvPolynomial (Fin 3) K) k =
        pderiv k F := by
      fin_cases k <;> rfl
    rw [hvec']
    simp_rw [hvec, pderiv_substLin, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single k]
    · have hsum : (∑ j : Fin 3, (MvPolynomial.C (N j k) : MvPolynomial (Fin 3) K) * MvPolynomial.C (M k j)) = 1 := by
        have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A k k) hMN
        rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
        calc ∑ j : Fin 3, (MvPolynomial.C (N j k) : MvPolynomial (Fin 3) K) * MvPolynomial.C (M k j)
            = MvPolynomial.C (∑ j : Fin 3, M k j * N j k) := by
              rw [map_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [← map_mul, mul_comm]
          _ = MvPolynomial.C 1 := by rw [h1]
          _ = 1 := map_one _
      calc ∑ j : Fin 3, MvPolynomial.C (N j k) * (MvPolynomial.C (M k j) * substLin M (pderiv k F))
          = (∑ j : Fin 3, MvPolynomial.C (N j k) * MvPolynomial.C (M k j)) *
              substLin M (pderiv k F) := by rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
        _ = substLin M (pderiv k F) := by rw [hsum, one_mul]
    · intro i _ hik
      have hsum : (∑ j : Fin 3, (MvPolynomial.C (N j k) : MvPolynomial (Fin 3) K) * MvPolynomial.C (M i j)) = 0 := by
        have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A i k) hMN
        rw [Matrix.mul_apply, Matrix.one_apply_ne hik] at h1
        calc ∑ j : Fin 3, (MvPolynomial.C (N j k) : MvPolynomial (Fin 3) K) * MvPolynomial.C (M i j)
            = MvPolynomial.C (∑ j : Fin 3, M i j * N j k) := by
              rw [map_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [← map_mul, mul_comm]
          _ = MvPolynomial.C 0 := by rw [h1]
          _ = 0 := map_zero _
      calc ∑ j : Fin 3, MvPolynomial.C (N j k) * (MvPolynomial.C (M i j) * substLin M (pderiv i F))
          = (∑ j : Fin 3, MvPolynomial.C (N j k) * MvPolynomial.C (M i j)) *
              substLin M (pderiv i F) := by rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hsum, zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  exact AlgHom.congr_fun hcomp P

theorem gaussPullback_isHomogeneous {F P : MvPolynomial (Fin 3) K} {m s : ℕ}
    (hF : F.IsHomogeneous m) (hP : P.IsHomogeneous s) :
    (gaussPullback F P).IsHomogeneous (s * (m - 1)) := by
  classical
  have hpd (i : Fin 3) : (pderiv i F).IsHomogeneous (m - 1) := hF.pderiv
  rw [P.as_sum, gaussPullback, map_sum, ← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun e he => ?_
  rw [mem_homogeneousSubmodule]
  have hedeg : e 0 + e 1 + e 2 = s := by
    have h := hP (MvPolynomial.mem_support_iff.mp he)
    rwa [weight_one_eq_sum, m3_sum] at h
  have hmon : MvPolynomial.monomial e (P.coeff e) =
      MvPolynomial.C (P.coeff e) * MvPolynomial.X 0 ^ e 0 *
        MvPolynomial.X 1 ^ e 1 * MvPolynomial.X 2 ^ e 2 := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.X,
      MvPolynomial.monomial_pow, MvPolynomial.monomial_pow, MvPolynomial.monomial_pow,
      MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial,
      MvPolynomial.monomial_mul_monomial]
    simp only [one_pow, mul_one, Finsupp.smul_single, smul_eq_mul]
    exact congrArg (fun d => MvPolynomial.monomial d (P.coeff e)) (by ext i; fin_cases i <;> simp)
  rw [hmon, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  change (MvPolynomial.C (P.coeff e) * pderiv 0 F ^ e 0 *
    pderiv 1 F ^ e 1 * pderiv 2 F ^ e 2).IsHomogeneous (s * (m - 1))
  have h0 := (MvPolynomial.isHomogeneous_C (Fin 3) (P.coeff e)).mul ((hpd 0).pow (e 0))
  have h1 := h0.mul ((hpd 1).pow (e 1))
  have h2 := h1.mul ((hpd 2).pow (e 2))
  have hdeg_eq : 0 + (m - 1) * e 0 + (m - 1) * e 1 + (m - 1) * e 2 = s * (m - 1) := by
    rw [zero_add, ← mul_add, ← mul_add, hedeg, mul_comm]
  rwa [hdeg_eq] at h2

/-- Any nonzero vector `a : Fin 3 → K` occurs as column `0` of an invertible `3 × 3` matrix. -/
private theorem exists_inv_matrix_col0 (a : Fin 3 → K) (ha : a ≠ 0) :
    ∃ M N : Matrix (Fin 3) (Fin 3) K, M * N = 1 ∧ N * M = 1 ∧ ∀ i, M i 0 = a i := by
  by_cases h0 : a 0 ≠ 0
  · let M : Matrix (Fin 3) (Fin 3) K := Matrix.of ![![a 0, 0, 0], ![a 1, 1, 0], ![a 2, 0, 1]]
    let N : Matrix (Fin 3) (Fin 3) K :=
      Matrix.of ![![(a 0)⁻¹, 0, 0], ![-(a 1) / a 0, 1, 0], ![-(a 2) / a 0, 0, 1]]
    refine ⟨M, N, ?_, ?_, ?_⟩
    · ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;> simp [M, N] <;> field_simp [h0] <;> ring
    · ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
      fin_cases i <;> fin_cases j <;> simp [M, N] <;> field_simp [h0] <;> ring
    · intro i; fin_cases i <;> rfl
  · push Not at h0
    by_cases h1 : a 1 ≠ 0
    · let M : Matrix (Fin 3) (Fin 3) K := Matrix.of ![![0, 1, 0], ![a 1, 0, 0], ![a 2, 0, 1]]
      let N : Matrix (Fin 3) (Fin 3) K :=
        Matrix.of ![![0, (a 1)⁻¹, 0], ![1, 0, 0], ![0, -(a 2) / a 1, 1]]
      refine ⟨M, N, ?_, ?_, ?_⟩
      · ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> simp [M, N, h1]
        field_simp [h1]; ring
      · ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> simp [M, N, h1]
      · intro i; fin_cases i <;> simp [M, h0]
    · push Not at h1
      have h2 : a 2 ≠ 0 := by
        intro h2
        apply ha; ext i; fin_cases i <;> assumption
      let M : Matrix (Fin 3) (Fin 3) K := Matrix.of ![![0, 1, 0], ![0, 0, 1], ![a 2, 0, 0]]
      let N : Matrix (Fin 3) (Fin 3) K := Matrix.of ![![0, 0, (a 2)⁻¹], ![1, 0, 0], ![0, 1, 0]]
      refine ⟨M, N, ?_, ?_, ?_⟩
      · ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> simp [M, N, h2]
      · ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> simp [M, N, h2]
      · intro i; fin_cases i <;> simp [M, h0, h1]

/-- A nonzero homogeneous polynomial of degree `m` cannot divide a nonzero homogeneous polynomial
of strictly smaller degree. -/
private theorem eq_zero_of_dvd_of_homog_lt {F L : MvPolynomial (Fin 3) K} {m d : ℕ}
    (hF : F.IsHomogeneous m) (hL : L.IsHomogeneous d) (hd : d < m)
    (hdvd : F ∣ L) : L = 0 := by
  by_contra hLne
  obtain ⟨Q, hQ⟩ := hdvd
  obtain ⟨k, hQk⟩ := isHomogeneous_of_dvd hL hLne ⟨F, by rw [hQ, mul_comm]⟩
  have hprod := hF.mul hQk
  rw [← hQ] at hprod
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hLne
  have h1 := hL (MvPolynomial.mem_support_iff.mp he)
  have h2 := hprod (MvPolynomial.mem_support_iff.mp he)
  omega

/-- Over an algebraically closed field, an irreducible homogeneous polynomial in 3 variables of
degree `m ≥ 2` cannot be independent of `X 0` (else it factors into linear forms in `X 1, X 2`). -/
private theorem not_indep_X0_of_irreducible [IsAlgClosed K] {F : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF_irr : Irreducible F) (hF_hom : F.IsHomogeneous m) (hm : 2 ≤ m)
    (hind : ∀ e ∈ F.support, e 0 = 0) : False := by
  classical
  -- `X 2` cannot divide `F` because `F` is irreducible of degree `m ≥ 2`.
  have hX2_ndvd : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ F := by
    intro ⟨Q, hQ⟩
    rcases hF_irr.isUnit_or_isUnit hQ with hu | hQu
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
      have h := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (Finsupp.single 2 1)) hc
      have hne : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 2 1 :=
        Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, hne] at h
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hQu
      have hdeg : F.IsHomogeneous 1 := by
        rw [hQ, hc]
        simpa using (MvPolynomial.isHomogeneous_X K (2 : Fin 3)).mul (MvPolynomial.isHomogeneous_C (Fin 3) c)
      obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hF_irr.ne_zero
      have h1 := hF_hom (MvPolynomial.mem_support_iff.mp he)
      have h2 := hdeg (MvPolynomial.mem_support_iff.mp he)
      omega
  -- Specialize `X 0 = 0, X 1 = X, X 2 = 1` to get a univariate polynomial `g : K[X]` of degree `m`.
  let evY : MvPolynomial (Fin 3) K →ₐ[K] K[X] := MvPolynomial.aeval ![0, Polynomial.X, 1]
  let g : K[X] := evY F
  have hg_coeff (j : ℕ) (hj : j ≤ m) :
      g.coeff j = F.coeff (Finsupp.single 1 j + Finsupp.single 2 (m - j)) := by
    dsimp only [g, evY]
    conv_lhs => rw [F.as_sum, map_sum, Polynomial.finsetSum_coeff]
    let target : Fin 3 →₀ ℕ := Finsupp.single 1 j + Finsupp.single 2 (m - j)
    have hterm (e : Fin 3 →₀ ℕ) (he : e ∈ F.support) :
        ((MvPolynomial.aeval ![0, Polynomial.X, 1]) (MvPolynomial.monomial e (F.coeff e))).coeff j =
          if e = target then F.coeff e else 0 := by
      rw [MvPolynomial.aeval_monomial, ← Polynomial.C_eq_algebraMap,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
      have h0 : (![0, Polynomial.X, 1] : Fin 3 → K[X]) 0 = 0 := rfl
      have h1v : (![0, Polynomial.X, 1] : Fin 3 → K[X]) 1 = Polynomial.X := rfl
      have h2 : (![0, Polynomial.X, 1] : Fin 3 → K[X]) 2 = 1 := rfl
      rw [h0, h1v, h2, hind e he, pow_zero, one_mul, one_pow, mul_one, Polynomial.coeff_C_mul_X_pow]
      have hesum : e 1 + e 2 = m := by
        have h := hF_hom (MvPolynomial.mem_support_iff.mp he)
        rw [weight_one_eq_sum, m3_sum, hind e he, zero_add] at h
        exact h
      by_cases h1 : j = e 1
      · have he_eq : e = target := by
          ext i; fin_cases i
          · simp [target, hind e he]
          · simp [target, h1]
          · simp [target]; omega
        simp [h1, he_eq]
      · have he_ne : e ≠ target := by
          intro heq
          apply h1
          have := congrArg (fun f : Fin 3 →₀ ℕ => f 1) heq
          simpa [target] using this.symm
        simp [h1, he_ne]
    rw [Finset.sum_congr rfl hterm]
    change (∑ e ∈ F.support, if e = target then F.coeff e else 0) = F.coeff target
    by_cases ht : target ∈ F.support
    · rw [Finset.sum_eq_single target]
      · simp
      · intro e _ het; simp [het]
      · intro h; exact absurd ht h
    · rw [MvPolynomial.notMem_support_iff.mp ht]
      apply Finset.sum_eq_zero
      intro e he
      have het : e ≠ target := fun h => ht (h ▸ he)
      simp [het]
  have hm_coeff : F.coeff (Finsupp.single 1 m) ≠ 0 := by
    intro h0
    apply hX2_ndvd
    -- Every `e ∈ F.support` has `e 0 = 0` and `e 1 + e 2 = m` and `e ≠ single 1 m`, so `e 2 ≥ 1`.
    refine ⟨∑ e ∈ F.support, MvPolynomial.monomial (e - Finsupp.single 2 1) (F.coeff e), ?_⟩
    rw [Finset.mul_sum]
    conv_lhs => rw [F.as_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hesum : e 1 + e 2 = m := by
      have h := hF_hom (MvPolynomial.mem_support_iff.mp he)
      rw [weight_one_eq_sum, m3_sum, hind e he, zero_add] at h
      exact h
    have he2 : 1 ≤ e 2 := by
      by_contra h2
      have he20 : e 2 = 0 := by omega
      have he_eq : e = Finsupp.single 1 m := by
        ext i; fin_cases i
        · simp [hind e he]
        · simp; omega
        · simp [he20]
      exact MvPolynomial.mem_support_iff.mp he (he_eq ▸ h0)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
    exact congrArg (fun d => MvPolynomial.monomial d (F.coeff e))
      (by ext i; fin_cases i <;> simp; omega)
  have hg_deg : 0 < g.natDegree := by
    have hgm : g.coeff m ≠ 0 := by
      rw [hg_coeff m le_rfl]
      simpa using hm_coeff
    have hle : m ≤ g.natDegree := Polynomial.le_natDegree_of_ne_zero hgm
    omega
  -- Over algebraically closed `K`, `g` has a root `r : K`.
  have hg_deg_ne : g.degree ≠ 0 := by
    have hg_ne : g ≠ 0 := by intro h0; rw [h0, Polynomial.natDegree_zero] at hg_deg; omega
    rw [Polynomial.degree_eq_natDegree hg_ne]
    exact_mod_cast hg_deg.ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g hg_deg_ne
  -- Shift `X 1 ↦ X 1 + r * X 2`: then `(substLin M F)` has zero `X 2^m` coefficient, so `X 1 ∣ F̃`.
  let M : Matrix (Fin 3) (Fin 3) K := ![![1, 0, 0], ![0, 1, r], ![0, 0, 1]]
  let N : Matrix (Fin 3) (Fin 3) K := ![![1, 0, 0], ![0, 1, -r], ![0, 0, 1]]
  have hMN : M * N = 1 := by
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [M, N]
  have hNM : N * M = 1 := by
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [M, N]
  let F' := substLin M F
  have hF'_hom : F'.IsHomogeneous m := substLin_isHomogeneous M hF_hom
  have hF'_ind0 : ∀ e ∈ F'.support, e 0 = 0 := by
    -- `substLin M` leaves `X 0` unchanged and maps `X 1, X 2` into `K[X 1, X 2]`.
    have hmem : F' ∈ Algebra.adjoin K ({MvPolynomial.X 1, MvPolynomial.X 2} : Set (MvPolynomial (Fin 3) K)) := by
      dsimp only [F']
      rw [F.as_sum, map_sum]
      refine Subalgebra.sum_mem _ fun e he => ?_
      rw [substLin, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three, hind e he, pow_zero, one_mul]
      refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.mul_mem _ ?_ ?_)
      · refine Subalgebra.pow_mem _ ?_ _
        have h1 : ∑ j : Fin 3, MvPolynomial.C (M 1 j) * MvPolynomial.X j =
            MvPolynomial.X 1 + MvPolynomial.C r * MvPolynomial.X 2 := by
          rw [Fin.sum_univ_three]; simp [M]
        rw [h1]
        exact Subalgebra.add_mem _ (Algebra.subset_adjoin (by simp))
          (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin (by simp)))
      · refine Subalgebra.pow_mem _ ?_ _
        have h2 : ∑ j : Fin 3, MvPolynomial.C (M 2 j) * MvPolynomial.X j = MvPolynomial.X 2 := by
          rw [Fin.sum_univ_three]; simp [M]
        rw [h2]
        exact Algebra.subset_adjoin (by simp)
    -- Every polynomial in `K[X 1, X 2]` has `e 0 = 0` on its support.
    have hsub : ∀ p ∈ Algebra.adjoin K ({MvPolynomial.X 1, MvPolynomial.X 2} : Set (MvPolynomial (Fin 3) K)),
        ∀ e ∈ p.support, e 0 = 0 := by
      intro p hp
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hp
      · rintro _ (rfl | rfl) e he
        · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at he
          split_ifs at he with h; · rw [← h]; simp
          · exact absurd rfl he
        · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at he
          split_ifs at he with h; · rw [← h]; simp
          · exact absurd rfl he
      · intro c e he
        rw [MvPolynomial.mem_support_iff, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C] at he
        split_ifs at he with h; · rw [← h]; simp
        · exact absurd rfl he
      · intro p q _ _ hp hq e he
        rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
        · exact hp e h
        · exact hq e h
      · intro p q _ _ hp hq e he
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at he
        obtain ⟨⟨a, b⟩, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
        have ha : a ∈ p.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)
        have hb : b ∈ q.support := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)
        have heq : a + b = e := Finset.mem_antidiagonal.mp hab
        rw [← heq, Finsupp.add_apply, hp a ha, hq b hb]
    exact hsub F' hmem
  -- Evaluate `F'` at `(0, 0, 1)`: equals `eval ![0, r, 1] F = g.eval r = 0`.
  have hF'_eval : MvPolynomial.eval ![0, 0, 1] F' = 0 := by
    have hcomp : (MvPolynomial.aeval (R := K) ![0, 0, 1]).comp (substLin M) =
        MvPolynomial.aeval (R := K) ![0, r, 1] := by
      apply MvPolynomial.algHom_ext; intro i
      rw [AlgHom.comp_apply, substLin_X, Fin.sum_univ_three]
      fin_cases i <;> simp [M]
    have h1 : MvPolynomial.eval ![0, 0, 1] F' = MvPolynomial.eval ![0, r, 1] F := by
      change (MvPolynomial.aeval (R := K) ![0, 0, 1]) (substLin M F) = _
      rw [← AlgHom.comp_apply, hcomp]; rfl
    have h2 : MvPolynomial.eval ![0, r, 1] F = g.eval r := by
      have hc : (Polynomial.aeval r).comp evY = MvPolynomial.aeval (R := K) ![0, r, 1] := by
        apply MvPolynomial.algHom_ext; intro i
        fin_cases i <;> simp [evY]
      change MvPolynomial.aeval (R := K) ![0, r, 1] F = _
      rw [← hc, AlgHom.comp_apply]; rfl
    rw [h1, h2]
    exact hr
  have hF'_coeff2 : F'.coeff (Finsupp.single 2 m) = 0 := by
    rw [← hF'_eval, MvPolynomial.eval_eq']
    rw [Finset.sum_eq_single (Finsupp.single 2 m)]
    · rw [Fin.prod_univ_three]; simp
    · intro e he hne
      have hesum : e 1 + e 2 = m := by
        have h := hF'_hom (MvPolynomial.mem_support_iff.mp he)
        rw [weight_one_eq_sum, m3_sum, hF'_ind0 e he, zero_add] at h
        exact h
      have he1 : 1 ≤ e 1 := by
        by_contra h1
        have he10 : e 1 = 0 := by omega
        apply hne; ext i; fin_cases i
        · simp [hF'_ind0 e he]
        · simp [he10]
        · simp; omega
      rw [Fin.prod_univ_three]
      simp [zero_pow (by omega : e 1 ≠ 0)]
    · intro hnot
      rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]
  -- Hence `X 1 ∣ F'`, contradicting irreducibility of `F'`.
  have hX1_dvd : (MvPolynomial.X 1 : MvPolynomial (Fin 3) K) ∣ F' := by
    refine ⟨∑ e ∈ F'.support, MvPolynomial.monomial (e - Finsupp.single 1 1) (F'.coeff e), ?_⟩
    rw [Finset.mul_sum]
    conv_lhs => rw [F'.as_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hesum : e 1 + e 2 = m := by
      have h := hF'_hom (MvPolynomial.mem_support_iff.mp he)
      rw [weight_one_eq_sum, m3_sum, hF'_ind0 e he, zero_add] at h
      exact h
    have he1 : 1 ≤ e 1 := by
      by_contra h1
      have he10 : e 1 = 0 := by omega
      have he_eq : e = Finsupp.single 2 m := by
        ext i; fin_cases i
        · simp [hF'_ind0 e he]
        · simp [he10]
        · simp; omega
      exact MvPolynomial.mem_support_iff.mp he (he_eq ▸ hF'_coeff2)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
    exact congrArg (fun d => MvPolynomial.monomial d (F'.coeff e))
      (by ext i; fin_cases i <;> simp; omega)
  have hF'_irr : Irreducible F' :=
    (MulEquiv.irreducible_iff (substLinEquiv M N hMN hNM).toMulEquiv).mpr hF_irr
  obtain ⟨Q, hQ⟩ := hX1_dvd
  rcases hF'_irr.isUnit_or_isUnit hQ with hu | hQu
  · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
    have h := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (Finsupp.single 1 1)) hc
    have hne : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 1 1 :=
      Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, hne] at h
  · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hQu
    have hdeg : F'.IsHomogeneous 1 := by
      rw [hQ, hc]
      simpa using (MvPolynomial.isHomogeneous_X K (1 : Fin 3)).mul (MvPolynomial.isHomogeneous_C (Fin 3) c)
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hF'_irr.ne_zero
    have h1 := hF'_hom (MvPolynomial.mem_support_iff.mp he)
    have h2 := hdeg (MvPolynomial.mem_support_iff.mp he)
    omega

/-- **Step 0 (`linear_polar_not_dvd`)**: Over an algebraically closed field `K` with
`∀ k, 0 < k → k ≤ m → (k : K) ≠ 0`, the three partial derivatives of an irreducible homogeneous
polynomial `F` of degree `m ≥ 2` are `K`-linearly independent modulo `F`. -/
theorem linear_polar_not_dvd [IsAlgClosed K] {F : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF_irr : Irreducible F) (hF_hom : F.IsHomogeneous m) (hm : 2 ≤ m)
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m → (k : K) ≠ 0)
    (a : Fin 3 → K) (ha : a ≠ 0) :
    ¬ (F ∣ ∑ i : Fin 3, MvPolynomial.C (a i) * pderiv i F) := by
  intro hdvd
  let L := ∑ i : Fin 3, MvPolynomial.C (a i) * pderiv i F
  have hL_hom : L.IsHomogeneous (m - 1) := by
    rw [← mem_homogeneousSubmodule]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mem_homogeneousSubmodule]
    simpa using (MvPolynomial.isHomogeneous_C (Fin 3) (a i)).mul hF_hom.pderiv
  have hL0 : L = 0 := eq_zero_of_dvd_of_homog_lt hF_hom hL_hom (by omega) hdvd
  obtain ⟨M, N, hMN, hNM, hM0⟩ := exists_inv_matrix_col0 a ha
  let F' := substLin M F
  have hF'_irr : Irreducible F' :=
    (MulEquiv.irreducible_iff (substLinEquiv M N hMN hNM).toMulEquiv).mpr hF_irr
  have hF'_hom : F'.IsHomogeneous m := substLin_isHomogeneous M hF_hom
  have hpd0 : pderiv 0 F' = 0 := by
    rw [pderiv_substLin]
    have hsum : ∑ i : Fin 3, MvPolynomial.C (M i 0) * substLin M (pderiv i F) = substLin M L := by
      dsimp only [L]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hM0 i, map_mul, substLin_C]
    rw [hsum, hL0, map_zero]
  have hind : ∀ e ∈ F'.support, e 0 = 0 := by
    intro e he
    by_contra he0
    have hpos : 0 < e 0 := Nat.pos_of_ne_zero he0
    have hle : e 0 ≤ m := by
      have h := hF'_hom (MvPolynomial.mem_support_iff.mp he)
      rw [weight_one_eq_sum, m3_sum] at h
      omega
    have hcoeff : (pderiv 0 F').coeff (e - Finsupp.single 0 1) = F'.coeff e * (e 0 : K) := by
      conv_lhs => rw [F'.as_sum, map_sum, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single e]
      · simp [pderiv_monomial]
      · intro e' he' hne
        rw [pderiv_monomial, MvPolynomial.coeff_monomial]
        split_ifs with heq
        · exfalso
          by_cases he'0 : e' 0 = 0
          · have hsub : e' - Finsupp.single 0 1 = e' := by ext i; fin_cases i <;> simp [he'0]
            rw [hsub] at heq
            have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) heq
            have h1 := hF'_hom (MvPolynomial.mem_support_iff.mp he)
            have h2 := hF'_hom (MvPolynomial.mem_support_iff.mp he')
            rw [weight_one_eq_sum, m3_sum] at h1 h2
            have h1' := congrArg (fun f : Fin 3 →₀ ℕ => f 1) heq
            have h2' := congrArg (fun f : Fin 3 →₀ ℕ => f 2) heq
            simp at h0 h1' h2'
            omega
          · apply hne
            ext i; fin_cases i
            · change e' 0 = e 0
              have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) heq; simp at h0; omega
            · change e' 1 = e 1
              have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 1) heq; simpa using h1
            · change e' 2 = e 2
              have h2 := congrArg (fun f : Fin 3 →₀ ℕ => f 2) heq; simpa using h2
        · rfl
      · intro h; exact absurd he h
    rw [hpd0] at hcoeff
    have hz : F'.coeff e * (e 0 : K) = 0 := by simpa using hcoeff.symm
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp he) (hchar (e 0) hpos hle) hz
  exact not_indep_X0_of_irreducible hF'_irr hF'_hom hm hind

/-- Over an algebraically closed field, a shear fixing `X 2` makes the `X 1^m` coefficient of an
irreducible homogeneous degree-`m` (`m ≥ 2`) polynomial nonzero. -/
theorem exists_shear_coeff_Y_ne_zero [IsAlgClosed K] {F : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF_irr : Irreducible F) (hF_hom : F.IsHomogeneous m) (hm : 2 ≤ m) :
    ∃ M N : Matrix (Fin 3) (Fin 3) K, M * N = 1 ∧ N * M = 1 ∧
      (substLin M F).coeff (Finsupp.single 1 m) ≠ 0 := by
  classical
  let h : K[X] := MvPolynomial.aeval ![Polynomial.X, 1, 0] F
  have hh_ne : h ≠ 0 := by
    intro hh0
    -- `h = 0` means every monomial of `F` has `e 2 ≥ 1`, so `X 2 ∣ F`.
    have hcoeff_all : ∀ e ∈ F.support, 1 ≤ e 2 := by
      intro e he
      by_contra h2
      have he2 : e 2 = 0 := by omega
      have hesum : e 0 + e 1 = m := by
        have h1 := hF_hom (MvPolynomial.mem_support_iff.mp he)
        rw [weight_one_eq_sum, m3_sum, he2, add_zero] at h1
        exact h1
      have hhe : h.coeff (e 0) = F.coeff e := by
        dsimp only [h]
        conv_lhs => rw [F.as_sum, map_sum, Polynomial.finsetSum_coeff]
        rw [Finset.sum_eq_single e]
        · rw [MvPolynomial.aeval_monomial, ← Polynomial.C_eq_algebraMap,
            Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
          simp [he2]
        · intro e' he' hne
          rw [MvPolynomial.aeval_monomial, ← Polynomial.C_eq_algebraMap,
            Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
          by_cases he'2 : e' 2 = 0
          · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
              one_pow, mul_one, he'2, pow_zero, Polynomial.coeff_C_mul_X_pow]
            split_ifs with h0
            · exfalso
              have he'sum : e' 0 + e' 1 = m := by
                have h1 := hF_hom (MvPolynomial.mem_support_iff.mp he')
                rw [weight_one_eq_sum, m3_sum, he'2, add_zero] at h1
                exact h1
              apply hne; ext i; fin_cases i
              · exact h0.symm
              · change e' 1 = e 1; omega
              · simp [he2, he'2]
            · rfl
          · simp [zero_pow he'2]
        · intro hnot; exact absurd he hnot
      rw [hh0, Polynomial.coeff_zero] at hhe
      exact MvPolynomial.mem_support_iff.mp he hhe.symm
    have hX2_dvd : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ F := by
      refine ⟨∑ e ∈ F.support, MvPolynomial.monomial (e - Finsupp.single 2 1) (F.coeff e), ?_⟩
      rw [Finset.mul_sum]; conv_lhs => rw [F.as_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      have he2 := hcoeff_all e he
      rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
      exact congrArg (fun d => MvPolynomial.monomial d (F.coeff e))
        (by ext i; fin_cases i <;> simp; omega)
    obtain ⟨Q, hQ⟩ := hX2_dvd
    rcases hF_irr.isUnit_or_isUnit hQ with hu | hQu
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
      have h1 := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (Finsupp.single 2 1)) hc
      have hne : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 2 1 :=
        Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, hne] at h1
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hQu
      have hdeg : F.IsHomogeneous 1 := by
        rw [hQ, hc]
        simpa using (MvPolynomial.isHomogeneous_X K (2 : Fin 3)).mul (MvPolynomial.isHomogeneous_C (Fin 3) c)
      obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hF_irr.ne_zero
      have h1 := hF_hom (MvPolynomial.mem_support_iff.mp he)
      have h2 := hdeg (MvPolynomial.mem_support_iff.mp he)
      omega
  obtain ⟨c, hc_not_root⟩ := Infinite.exists_notMem_finset h.roots.toFinset
  have hc_eval : h.eval c ≠ 0 := by
    intro h0
    exact hc_not_root (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hh_ne).mpr h0))
  let M : Matrix (Fin 3) (Fin 3) K := ![![1, c, 0], ![0, 1, 0], ![0, 0, 1]]
  let N : Matrix (Fin 3) (Fin 3) K := ![![1, -c, 0], ![0, 1, 0], ![0, 0, 1]]
  have hMN : M * N = 1 := by
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [M, N]
  have hNM : N * M = 1 := by
    ext i j; rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [M, N]
  refine ⟨M, N, hMN, hNM, ?_⟩
  let F' := substLin M F
  have hF'_hom : F'.IsHomogeneous m := substLin_isHomogeneous M hF_hom
  have heval_eq : MvPolynomial.eval ![0, 1, 0] F' = h.eval c := by
    have hcomp1 : (MvPolynomial.aeval (R := K) ![0, 1, 0]).comp (substLin M) =
        MvPolynomial.aeval (R := K) ![c, 1, 0] := by
      apply MvPolynomial.algHom_ext; intro i
      rw [AlgHom.comp_apply, substLin_X, Fin.sum_univ_three]
      fin_cases i <;> simp [M]
    have hcomp2 : (Polynomial.aeval c).comp (MvPolynomial.aeval (R := K) ![Polynomial.X, 1, 0]) =
        MvPolynomial.aeval (R := K) ![c, 1, 0] := by
      apply MvPolynomial.algHom_ext; intro i
      fin_cases i <;> simp
    change MvPolynomial.aeval (R := K) ![0, 1, 0] (substLin M F) = Polynomial.aeval c h
    rw [← AlgHom.comp_apply, hcomp1, ← hcomp2, AlgHom.comp_apply]
  have hcoeff_eq : MvPolynomial.eval ![0, 1, 0] F' = F'.coeff (Finsupp.single 1 m) := by
    rw [MvPolynomial.eval_eq']
    rw [Finset.sum_eq_single (Finsupp.single 1 m)]
    · rw [Fin.prod_univ_three]; simp
    · intro e he hne
      have hesum : e 0 + e 1 + e 2 = m := by
        have h1 := hF'_hom (MvPolynomial.mem_support_iff.mp he)
        rwa [weight_one_eq_sum, m3_sum] at h1
      have h02 : e 0 ≠ 0 ∨ e 2 ≠ 0 := by
        by_contra hboth; push Not at hboth
        apply hne; ext i; fin_cases i
        · simp [hboth.1]
        · simp; omega
        · simp [hboth.2]
      rw [Fin.prod_univ_three]
      rcases h02 with h0 | h2
      · simp [zero_pow h0]
      · simp [zero_pow h2]
    · intro hnot; rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]
  rw [← hcoeff_eq, heval_eq]
  exact hc_eval

end LinearChanges

#print axioms substLin_isHomogeneous
#print axioms pderiv_substLin
#print axioms gaussPullback_substLin
#print axioms gaussPullback_isHomogeneous
#print axioms linear_polar_not_dvd
#print axioms exists_shear_coeff_Y_ne_zero

end ArkLib.ProximityGap.Frontier.PlaneCurveLinearAlgebra
