/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# The general (`l × l`) Wronskian of a family of polynomials (#389, Stepanov route)

Mathlib has only the two-element `Polynomial.wronskian` (for Mason–Stothers).  The Stepanov
method for bounding multiplicative-subgroup intersections (Garcia–Voloch / Heath-Brown–
Konyagin, the named `GVRepBound` input) requires the **general `l × l` Wronskian** and its
linear-independence criterion — the non-vanishing of the Stepanov auxiliary polynomial is
exactly an `l × l` Wronskian computation (Shkredov–Vyugin, *On additive shifts of
multiplicative subgroups*, Lemma 3.1 / Prop 3.2).

This file builds that foundation:

* `wronskianMatrix f` — the matrix `(i, j) ↦ derivative^[i] (f j)`.
* `wronskianDet f` — its determinant.
* `wronskianDet_eq_zero_of_dependent` — **the key criterion**: if a *constant-coefficient*
  linear combination `∑_j μ_j · f_j` vanishes with `μ ≠ 0`, the Wronskian is zero.  Equivalently
  (contrapositive `wronskianDet_ne_zero_imp_linearIndependent`) a nonzero Wronskian certifies
  linear independence of `f` — the engine for proving the Stepanov generators independent.
* `natDegree_wronskianDet_le` — the precise degree bound `deg W ≤ ∑_j deg f_j − C(l,2)` (the input to the SV degree contradiction).
-/

open Polynomial Matrix Finset

namespace ArkLib.ProximityGap.Wronskian

variable {R : Type*} [CommRing R] {l : ℕ}

/-- The `l × l` Wronskian matrix of a family `f : Fin l → R[X]`: entry `(i, j)` is the
`i`-th derivative of `f j`. -/
noncomputable def wronskianMatrix (f : Fin l → R[X]) : Matrix (Fin l) (Fin l) R[X] :=
  fun i j => (Polynomial.derivative^[(i : ℕ)]) (f j)

/-- The general Wronskian determinant of a family of polynomials. -/
noncomputable def wronskianDet (f : Fin l → R[X]) : R[X] :=
  (wronskianMatrix f).det

@[simp] theorem wronskianMatrix_apply (f : Fin l → R[X]) (i j : Fin l) :
    wronskianMatrix f i j = (Polynomial.derivative^[(i : ℕ)]) (f j) := rfl

/-- The mul-vec of the Wronskian matrix by a constant vector is the derivative-column of the
corresponding combination: `(W ⬝ᵥ (C ∘ μ)) i = derivative^[i] (∑_j μ_j · f_j)`. -/
theorem wronskianMatrix_mulVec_C (f : Fin l → R[X]) (μ : Fin l → R) (i : Fin l) :
    (wronskianMatrix f).mulVec (fun j => C (μ j)) i
      = (Polynomial.derivative^[(i : ℕ)]) (∑ j, C (μ j) * f j) := by
  rw [Matrix.mulVec, dotProduct]
  rw [iterate_derivative_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [wronskianMatrix_apply, iterate_derivative_C_mul, mul_comm]

/-- **The key criterion**: a vanishing constant-coefficient combination forces the Wronskian
to vanish.  (Over a domain; the contrapositive certifies linear independence.) -/
theorem wronskianDet_eq_zero_of_dependent [IsDomain R] {f : Fin l → R[X]} {μ : Fin l → R}
    (hμ : μ ≠ 0) (hdep : ∑ j, C (μ j) * f j = 0) :
    wronskianDet f = 0 := by
  classical
  rw [wronskianDet]
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun j => C (μ j), ?_, ?_⟩
  · intro h
    apply hμ
    funext j
    have := congrFun h j
    simpa using (Polynomial.C_eq_zero.mp this)
  · funext i
    rw [wronskianMatrix_mulVec_C, hdep, iterate_derivative_zero]
    rfl

/-- **Linear independence from a nonzero Wronskian**: if `wronskianDet f ≠ 0` then no nonzero
constant combination of the `f j` vanishes — the certificate the Stepanov construction needs. -/
theorem linearIndependent_of_wronskianDet_ne_zero [IsDomain R] {f : Fin l → R[X]}
    (hW : wronskianDet f ≠ 0) {μ : Fin l → R} (hdep : ∑ j, C (μ j) * f j = 0) :
    μ = 0 := by
  by_contra hμ
  exact hW (wronskianDet_eq_zero_of_dependent hμ hdep)

/-- **Bridge to `LinearIndependent`**: a nonzero Wronskian gives Mathlib's `LinearIndependent F f`
in the exact form the in-tree Stepanov existence engine (`exists_highMult_vanisher`) consumes.
Over a field the `F`-scalar action on `F[X]` is `a • p = C a * p`, so this is the packaged
form of `linearIndependent_of_wronskianDet_ne_zero`. -/
theorem linearIndependent_of_wronskianDet_ne_zero' {F : Type*} [Field F] {f : Fin l → F[X]}
    (hW : wronskianDet f ≠ 0) : LinearIndependent F f := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : ∑ j, C (c j) * f j = 0 := by
    simpa only [Polynomial.smul_eq_C_mul] using hc
  have h0 := linearIndependent_of_wronskianDet_ne_zero hW hc'
  intro i; rw [h0]; rfl

/-- The sum of `σ i` over a permutation of `Fin l` is `C(l, 2)`. -/
theorem sum_perm_eq_choose_two (σ : Equiv.Perm (Fin l)) :
    ∑ i : Fin l, (σ i : ℕ) = l.choose 2 := by
  rw [Equiv.sum_comp σ (fun i : Fin l => (i : ℕ)),
    Fin.sum_univ_eq_sum_range (fun i => i) l, Finset.sum_range_id, Nat.choose_two_right]

/-- **The precise Wronskian degree bound** `deg(wronskianDet f) ≤ ∑_j deg(f j) − C(l, 2)`,
the input to the Stepanov degree contradiction.  Each of the `l` derivative-rows drops the
degree by one more, removing `0 + 1 + ⋯ + (l−1) = C(l,2)` from the naive product bound. -/
theorem natDegree_wronskianDet_le (f : Fin l → R[X]) :
    (wronskianDet f).natDegree ≤ (∑ j, (f j).natDegree) - l.choose 2 := by
  classical
  rw [wronskianDet, Matrix.det_apply]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun σ _ => ?_⟩
  simp only [Function.comp_apply]
  have hsmul : (Equiv.Perm.sign σ • ∏ i, wronskianMatrix f (σ i) i).natDegree
      = (∏ i, wronskianMatrix f (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with sg | sg
    · rw [sg, one_smul]
    · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
  rw [hsmul]
  by_cases hprod : (∏ i, wronskianMatrix f (σ i) i) = 0
  · rw [hprod, natDegree_zero]; exact Nat.zero_le _
  · have hfac : ∀ i, (σ i : ℕ) ≤ (f i).natDegree := by
      intro i
      by_contra h
      simp only [not_le] at h
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [wronskianMatrix_apply]; exact Polynomial.iterate_derivative_eq_zero h))
    have hterm : ∀ i, (wronskianMatrix f (σ i) i).natDegree ≤ (f i).natDegree - (σ i : ℕ) := by
      intro i; rw [wronskianMatrix_apply]; exact Polynomial.natDegree_iterate_derivative _ _
    have hcombined : ∑ i, ((f i).natDegree - (σ i : ℕ)) = (∑ j, (f j).natDegree) - l.choose 2 := by
      have h1 : ∑ i, ((f i).natDegree - (σ i : ℕ)) + l.choose 2 = ∑ j, (f j).natDegree := by
        rw [← sum_perm_eq_choose_two σ, ← Finset.sum_add_distrib,
          Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hfac i))]
      omega
    rw [← hcombined]
    exact le_trans (Polynomial.natDegree_prod_le _ _) (Finset.sum_le_sum (fun i _ => hterm i))

/-- Differentiating `i` times drops the order of vanishing at `α` by at most `i`:
`(X − α)^k ∣ f ⟹ (X − α)^(k − i) ∣ derivative^[i] f`. -/
theorem pow_sub_dvd_iterate_derivative {α : R} {k : ℕ} {f : R[X]}
    (h : (X - C α) ^ k ∣ f) : ∀ i, (X - C α) ^ (k - i) ∣ (Polynomial.derivative^[i]) f := by
  intro i
  induction i with
  | zero => simpa using h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    by_cases hki : k ≤ i
    · rw [Nat.sub_eq_zero_of_le (le_trans hki (Nat.le_succ i)), pow_zero]; exact one_dvd _
    · rw [not_le] at hki
      obtain ⟨g, hg⟩ := ih
      rw [hg, derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C,
        sub_zero, mul_one]
      have hpow : k - i = (k - (i + 1)) + 1 := by omega
      rw [hpow]
      refine dvd_add ?_ ?_
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _) _
      · exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

/-- **The Wronskian divisibility**: if every `f j` is divisible by `(X − α)^k` (and `l ≤ k+1`,
so the `l` derivative-rows don't exhaust the order), the Wronskian is divisible by
`(X − α)^(l·k − C(l,2))`.  With `natDegree_wronskianDet_le` this is the two-sided
degree/order squeeze driving the Stepanov linear-independence contradiction (the genuine
`n ∣ p−1` split-case wall). -/
theorem pow_dvd_wronskianDet {α : R} {k : ℕ} {f : Fin l → R[X]}
    (hk : l ≤ k + 1) (hdvd : ∀ j, (X - C α) ^ k ∣ f j) :
    (X - C α) ^ (l * k - l.choose 2) ∣ wronskianDet f := by
  classical
  rw [wronskianDet, Matrix.det_apply]
  refine Finset.dvd_sum (fun σ _ => ?_)
  have hexp : l * k - l.choose 2 = ∑ i : Fin l, (k - (σ i : ℕ)) := by
    have hle : ∀ i : Fin l, (σ i : ℕ) ≤ k := fun i => Nat.lt_succ_iff.mp (lt_of_lt_of_le (σ i).isLt hk)
    have hsum : ∑ i : Fin l, (k - (σ i : ℕ)) + l.choose 2 = l * k := by
      rw [← sum_perm_eq_choose_two σ, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hle i)), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    omega
  have hprod : (X - C α) ^ (l * k - l.choose 2) ∣ ∏ i : Fin l, wronskianMatrix f (σ i) i := by
    rw [hexp]
    calc (X - C α) ^ (∑ i : Fin l, (k - (σ i : ℕ)))
        = ∏ i : Fin l, (X - C α) ^ (k - (σ i : ℕ)) :=
          (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => k - (σ i : ℕ)) (X - C α)).symm
      _ ∣ ∏ i : Fin l, wronskianMatrix f (σ i) i :=
          Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => by
            rw [wronskianMatrix_apply]; exact pow_sub_dvd_iterate_derivative (hdvd i) (σ i))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with sg | sg
  · rw [sg, one_smul]; exact hprod
  · rw [sg, Units.neg_smul, one_smul]; exact dvd_neg.mpr hprod

end ArkLib.ProximityGap.Wronskian
