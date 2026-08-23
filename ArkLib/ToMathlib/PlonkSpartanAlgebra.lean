/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Plonk / Spartan / RingSwitching algebra

* `Finset.prod_div_perm_eq_one_of_eq_comp` — the Plonk **grand-product permutation identity**
  (#115): if `num = den ∘ e` for a permutation `e`, the accumulator `(∏ num)/(∏ den) = 1`.
* `Polynomial.eval_prod_X_sub_C_eq_zero_iff_mem` — the **vanishing polynomial**
  `Z_H = ∏_{b∈H}(X-C b)` characterization (#114/#115):
  `eval a Z_H = 0 ↔ a ∈ H` over an integral domain.
* `MvPolynomial.eval_eqIndicator_prod_boolean` — the multilinear **eq-indicator** is a
  Kronecker delta on the boolean cube (#114 Spartan):
  `eval x (∏ᵢ ((1-Xᵢ)(1-yᵢ)+Xᵢ yᵢ)) = if x = y then 1 else 0`.
* `MvPolynomial.sum_eval_eqIndicator_prod_boolean` /
  `MvPolynomial.sum_weighted_eval_eqIndicator_prod_boolean` — summing that eq-indicator over the
  boolean cube gives `1`, and a weighted sum selects the target value `f y`.
* `MvPolynomial.sum_eval_eqPolynomial_zeroOne` /
  `MvPolynomial.sum_weighted_eval_eqPolynomial_zeroOne` — the same selector interfaces for the
  in-tree `eqPolynomial` notation consumed by Spartan/MLE code.
* `Finset.prod_fin_add_dite_split` — a product over `Fin (ℓ+κ)` that is `Fp` on the `κ`-prefix and
  `Fs` on the `ℓ`-suffix factors as `(∏ Fp)·(∏ Fs)` (#19/#29/#33/#62, dedups RingSwitching/Binius).
-/

open Finset

namespace Finset

/-- Plonk grand-product permutation identity. -/
theorem prod_div_perm_eq_one_of_eq_comp {ι G : Type*} [Fintype ι] [CommGroup G]
    (num den : ι → G) (e : ι ≃ ι) (h : ∀ i, num i = den (e i)) :
    (∏ i, num i) / (∏ i, den i) = 1 := by
  rw [div_eq_one, Finset.prod_congr rfl (fun i _ => h i), Equiv.prod_comp]

/-- Product over `Fin (ℓ+κ)` that is `Fp` on the `κ`-prefix and `Fs` on the `ℓ`-suffix. -/
theorem prod_fin_add_dite_split {M : Type*} [CommMonoid M] {κ ℓ : ℕ}
    (Fp : Fin κ → M) (Fs : Fin ℓ → M) :
    (∏ i : Fin (ℓ + κ), if h : i.val < κ then Fp ⟨i.val, h⟩ else Fs ⟨i.val - κ, by omega⟩)
      = (∏ i, Fp i) * ∏ j, Fs j := by
  rw [← (finCongr (Nat.add_comm κ ℓ)).prod_comp
      (fun i : Fin (ℓ + κ) => if h : i.val < κ then Fp ⟨i.val, h⟩ else Fs ⟨i.val - κ, by omega⟩),
      Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hlt : ((finCongr (Nat.add_comm κ ℓ)) (Fin.castAdd ℓ i)).val < κ := by simpa using i.isLt
    rw [dif_pos hlt]; congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    have hge : ¬ ((finCongr (Nat.add_comm κ ℓ)) (Fin.natAdd κ j)).val < κ := by simp
    rw [dif_neg hge]; congr 1; apply Fin.ext; simp

end Finset

namespace Polynomial

/-- Vanishing polynomial root characterization: `eval a (∏_{b∈H}(X - C b)) = 0 ↔ a ∈ H`. -/
theorem eval_prod_X_sub_C_eq_zero_iff_mem {R : Type*} [CommRing R] [IsDomain R]
    (H : Finset R) (a : R) :
    Polynomial.eval a (∏ b ∈ H, (Polynomial.X - Polynomial.C b)) = 0 ↔ a ∈ H := by
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨b, hb, hba⟩; rwa [sub_eq_zero.mp hba]
  · intro ha; exact ⟨a, ha, by simp⟩

end Polynomial

namespace MvPolynomial

/-- The multilinear eq-indicator evaluated at a boolean point is the Kronecker delta `[x = y]`. -/
theorem eval_eqIndicator_prod_boolean {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]
    (x y : σ → Fin 2) :
    MvPolynomial.eval (fun i => (x i : R))
      (∏ i : σ, ((1 - MvPolynomial.X i) * (1 - MvPolynomial.C ((y i : R)))
        + MvPolynomial.X i * MvPolynomial.C ((y i : R)))) =
      if x = y then 1 else 0 := by
  rw [MvPolynomial.eval_prod]
  simp only [map_add, map_mul, map_sub, map_one, MvPolynomial.eval_X, MvPolynomial.eval_C]
  by_cases hxy : x = y
  · subst hxy; rw [if_pos rfl]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have : x i = 0 ∨ x i = 1 := by omega
    rcases this with h | h <;> rw [h] <;> simp
  · rw [if_neg hxy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    have hx : x j = 0 ∨ x j = 1 := by omega
    have hy : y j = 0 ∨ y j = 1 := by omega
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> simp_all

/-- The eq-indicator has total mass `1` over the boolean cube. -/
theorem sum_eval_eqIndicator_prod_boolean {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] (y : σ → Fin 2) :
    (∑ x : σ → Fin 2,
      MvPolynomial.eval (fun i => (x i : R))
        (∏ i : σ, ((1 - MvPolynomial.X i) * (1 - MvPolynomial.C ((y i : R)))
          + MvPolynomial.X i * MvPolynomial.C ((y i : R))))) = 1 := by
  classical
  calc
    (∑ x : σ → Fin 2,
      MvPolynomial.eval (fun i => (x i : R))
        (∏ i : σ, ((1 - MvPolynomial.X i) * (1 - MvPolynomial.C ((y i : R)))
          + MvPolynomial.X i * MvPolynomial.C ((y i : R)))))
        = ∑ x : σ → Fin 2, (if x = y then (1 : R) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            exact MvPolynomial.eval_eqIndicator_prod_boolean x y
    _ = 1 := by
        simp

/-- A weighted sum against the eq-indicator selects the target boolean-cube value. -/
theorem sum_weighted_eval_eqIndicator_prod_boolean {σ R : Type*} [Fintype σ]
    [DecidableEq σ] [CommRing R] (f : (σ → Fin 2) → R) (y : σ → Fin 2) :
    (∑ x : σ → Fin 2,
      f x * MvPolynomial.eval (fun i => (x i : R))
        (∏ i : σ, ((1 - MvPolynomial.X i) * (1 - MvPolynomial.C ((y i : R)))
          + MvPolynomial.X i * MvPolynomial.C ((y i : R))))) = f y := by
  classical
  calc
    (∑ x : σ → Fin 2,
      f x * MvPolynomial.eval (fun i => (x i : R))
        (∏ i : σ, ((1 - MvPolynomial.X i) * (1 - MvPolynomial.C ((y i : R)))
          + MvPolynomial.X i * MvPolynomial.C ((y i : R)))))
        = ∑ x : σ → Fin 2, f x * (if x = y then (1 : R) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [MvPolynomial.eval_eqIndicator_prod_boolean x y]
    _ = f y := by
        simp [mul_ite]

/-- The in-tree `eqPolynomial` has total mass `1` over the boolean cube. -/
theorem sum_eval_eqPolynomial_zeroOne {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommRing R] (y : σ → Fin 2) :
    (∑ x : σ → Fin 2,
      MvPolynomial.eval (x : σ → R) (MvPolynomial.eqPolynomial y)) = 1 := by
  classical
  calc
    (∑ x : σ → Fin 2,
      MvPolynomial.eval (x : σ → R) (MvPolynomial.eqPolynomial y))
        = ∑ x : σ → Fin 2, (if x = y then (1 : R) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            exact MvPolynomial.eqPolynomial_eval_zeroOne y x
    _ = 1 := by
        simp

/-- A weighted sum against the in-tree `eqPolynomial` selects the target boolean-cube value. -/
theorem sum_weighted_eval_eqPolynomial_zeroOne {σ R : Type*} [Fintype σ]
    [DecidableEq σ] [CommRing R] (f : (σ → Fin 2) → R) (y : σ → Fin 2) :
    (∑ x : σ → Fin 2,
      f x * MvPolynomial.eval (x : σ → R) (MvPolynomial.eqPolynomial y)) = f y := by
  classical
  calc
    (∑ x : σ → Fin 2,
      f x * MvPolynomial.eval (x : σ → R) (MvPolynomial.eqPolynomial y))
        = ∑ x : σ → Fin 2, f x * (if x = y then (1 : R) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [MvPolynomial.eqPolynomial_eval_zeroOne y x]
    _ = f y := by
        simp [mul_ite]

end MvPolynomial

#print axioms Finset.prod_div_perm_eq_one_of_eq_comp
#print axioms Finset.prod_fin_add_dite_split
#print axioms Polynomial.eval_prod_X_sub_C_eq_zero_iff_mem
#print axioms MvPolynomial.eval_eqIndicator_prod_boolean
#print axioms MvPolynomial.sum_eval_eqIndicator_prod_boolean
#print axioms MvPolynomial.sum_weighted_eval_eqIndicator_prod_boolean
#print axioms MvPolynomial.sum_eval_eqPolynomial_zeroOne
#print axioms MvPolynomial.sum_weighted_eval_eqPolynomial_zeroOne
