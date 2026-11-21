/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarMomentCoordinates
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # The coordinates of a minimal kernel vector of an affine pencil -/

set_option autoImplicit false
open Finset Polynomial Matrix
namespace ProximityGap.ApolarAffineKernelSpan
variable {K I J : Type*} [Field K] [Fintype J]

private noncomputable def low (l : ℕ) (p : K[X]) : K[X] :=
  ∑ i ∈ range l, monomial i (p.coeff i)

private theorem coeff_low (l j : ℕ) (p : K[X]) :
    (low l p).coeff j = if j<l then p.coeff j else 0 := by
  classical
  simp [low,finsetSum_coeff,coeff_monomial,Finset.sum_ite_eq']

private theorem low_degree {l : ℕ} (hl : 0<l) (p : K[X]) : (low l p).natDegree<l := by
  by_contra! h
  have hh := coeff_low l (low l p).natDegree p
  simp only [h.not_gt,ite_false,coeff_natDegree,leadingCoeff_eq_zero] at hh
  simp [hh] at h
  omega

/-- If every lower-degree polynomial kernel vector is zero, there can be
no missing coefficient in degree l of the product H·v for nonzero H of
degree at most l. -/
theorem separated (M : Matrix I J K[X]) (v : J → K[X]) {l : ℕ} (hl : 0<l)
    (hA : ∀ i j, (M i j).natDegree≤1) (hv : M *ᵥ v=0)
    (hmin : ∀ q : J → K[X], M *ᵥ q=0 → (∀ j, (q j).natDegree<l) → q=0)
    (hfree : ∃ j, (v j).eval 0≠0) (H : K[X]) (hH : H.natDegree≤l)
    (hgap : ∀ j, (H*v j).coeff l=0) : H=0 := by
  classical
  let q := fun j : J => low l (H*v j)
  have hqj (j : J) : (q j).natDegree<l := low_degree hl _
  have hd (j : J) : X^(l+1) ∣ H*v j-q j := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    rw [coeff_sub,show (q j).coeff i = _ from coeff_low l i (H*v j)]
    split_ifs with h
    · exact sub_self _
    · rw [show i=l by omega,hgap,sub_zero]
  have hk : M *ᵥ q=0 := by
    funext i
    have hsum : ∑ j, M i j*(H*v j)=0 := by
      have hh := congrFun hv i
      change ∑ j, M i j*v j=0 at hh
      calc
        _ = H * ∑ j, M i j*v j := by rw [mul_sum]; apply sum_congr rfl; intros; ring
        _ = 0 := by rw [hh,mul_zero]
    have hdvd : X^(l+1) ∣ ∑ j, M i j*(H*v j-q j) :=
      Finset.dvd_sum fun j _ => (hd j).mul_left _
    simp only [mul_sub,sum_sub_distrib,hsum,zero_sub,dvd_neg] at hdvd
    change ∑ j, M i j*q j=0
    by_contra hne
    have bound : (∑ j, M i j*q j).natDegree≤l := by
      apply natDegree_sum_le_of_forall_le
      intro j _
      exact natDegree_mul_le.trans (by have := hA i j; have := hqj j; omega)
    have := natDegree_le_of_dvd hdvd hne
    rw [natDegree_X_pow] at this
    omega
  have hq := hmin q hk hqj
  obtain ⟨j,hj⟩ := hfree
  have hprod := hd j
  rw [congrFun hq j,Pi.zero_apply,sub_zero] at hprod
  have hcop : IsCoprime (X : K[X]) (v j) := irreducible_X.coprime_iff_not_dvd.mpr (by
    intro h
    exact hj (by simpa only [← coeff_zero_eq_eval_zero] using (X_dvd_iff.mp h)))
  have hdiv : X^(l+1) ∣ H := hcop.pow_left.dvd_of_dvd_mul_right hprod
  by_contra hne
  have := natDegree_le_of_dvd hdiv hne
  rw [natDegree_X_pow] at this
  omega

/-- An affine pencil's minimal primitive degree-l nullvector has coordinate
entries spanning all monomials through degree l. -/
theorem monomials (M : Matrix I J K[X]) (v : J → K[X]) {l : ℕ} (hl : 0<l)
    (hA : ∀ i j, (M i j).natDegree≤1) (hv : M *ᵥ v=0) (hvl : ∀ j, (v j).natDegree≤l)
    (hmin : ∀ q : J → K[X], M *ᵥ q=0 → (∀ j, (q j).natDegree<l) → q=0)
    (hfree : ∃ j, (v j).eval 0≠0) (a : ℕ) (ha : a≤l) :
    ∃ c : J → K, ∑ j, C (c j)*v j = X^a := by
  classical
  let A : Matrix J (Fin (l+1)) K := fun j i => (v j).coeff i.val
  have ht : Function.Injective A.mulVecLin := by
    apply LinearMap.ker_eq_bot.1
    apply LinearMap.ker_eq_bot'.2
    intro b hb
    let H : K[X] := ∑ i : Fin (l+1), C (b i)*X^(l-i.val)
    have hbnd : H.natDegree≤l := by
      apply natDegree_sum_le_of_forall_le
      intro i _
      exact (natDegree_C_mul_le ..).trans ((natDegree_X_pow_le _).trans (Nat.sub_le ..))
    have hH := separated M v hl hA hv hmin hfree H hbnd (by
      intro j
      have h := congrFun hb j
      change ∑ i, (v j).coeff i.val*b i=0 at h
      calc
        _ = ∑ i : Fin (l+1), (v j).coeff i.val*b i := by
          simp only [H,sum_mul,finsetSum_coeff]
          apply sum_congr rfl
          intro i _
          rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul']
          simp [show l-(l-i.val)=i.val by have := i.isLt; omega,mul_comm]
        _ = 0 := h)
    funext i
    have hc := congrArg (fun p : K[X] => p.coeff (l-i.val)) hH
    simp only [H,finsetSum_coeff,coeff_C_mul_X_pow,coeff_zero] at hc
    rw [sum_eq_single i] at hc
    · simpa using hc
    · intro j _ hji
      simp [show l-i.val≠l-j.val by
        intro he
        apply hji
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        omega]
    · simp
  have rank : Aᵀ.rank=Module.finrank K (Fin (l+1) → K) :=
    A.rank_transpose.trans (LinearMap.finrank_range_of_inj ht)
  have sur := LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq
    (show Module.finrank K (LinearMap.range Aᵀ.mulVecLin)=_ from rank))
  obtain ⟨c,hc⟩ := sur (fun i : Fin (l+1) => if i.val=a then 1 else 0)
  refine ⟨c,?_⟩
  ext i
  simp only [finsetSum_coeff,coeff_C_mul,coeff_X_pow]
  by_cases hi : i<l+1
  · have h := congrFun hc ⟨i,hi⟩
    change ∑ j, (v j).coeff i*c j = _ at h
    simpa only [mul_comm] using h
  · have hv0 (j : J) : (v j).coeff i=0 := coeff_eq_zero_of_natDegree_lt (by have := hvl j; omega)
    simp [hv0,show i≠a by omega]

#print axioms separated
#print axioms monomials
end ProximityGap.ApolarAffineKernelSpan
