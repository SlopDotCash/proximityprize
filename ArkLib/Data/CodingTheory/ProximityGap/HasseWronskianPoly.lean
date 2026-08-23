/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HasseWronskianMonomial

/-!
# The classical (Hasse) Wronskian of distinct-degree polynomials is nonzero (#389)

Generalising `hasseWronskian_monomial_ne_zero` from monomials to arbitrary polynomials: for nonzero
`P : Fin l → F[X]` whose degrees `dⱼ := natDegree (P j)` are **distinct in `F`**, the classical
Hasse-Wronskian determinant

  `W := det[ hasseDeriv a (P j) ]_{a,j}`  satisfies  `W ≠ 0`.

The coefficient at `D = ∑dⱼ − l(l−1)/2` is `(∏ⱼ lead Pⱼ) · det[C(dⱼ,a)]`: only the leading monomials
of the `Pⱼ` reach degree `D` in the determinant (`coeff_prod_at_sum`, the non-uniform
coefficient-of-product lemma), and `hasseDeriv a (Pⱼ)` contributes `C(dⱼ,a)·lead Pⱼ` at its top
degree `dⱼ−a` (`hasseDeriv_coeff`). Both factors are nonzero: `lead Pⱼ ≠ 0` since `Pⱼ ≠ 0`, and
`det[C(dⱼ,a)] ≠ 0` by `det_choose_ne_zero` when the `dⱼ` are distinct in `F`.

## Role in #389

This is the **complete classical (derivative) analogue of GK16's proven folded (dilation) Wronskian
non-vanishing** `ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent`, for distinct-degree
families. The classical Wronskian is the non-vanishing tool of the Shkredov–Vyugin / Heath-Brown–
Konyagin additive-shift Stepanov argument (which bounds `|R ∩ (R+μ)|`, hence the additive energy of
`μ_n`, hence the sub-Johnson list / supply wall). The remaining layers toward `GVRepBound`: lift to
**general** linearly-independent families via `GK16Finish.exists_distinctDegree_recombination` (which
reduces any independent family to a distinct-degree one by an invertible recombination), then the SV11
multiplicity-on-`V` construction.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- Non-uniform coefficient-of-product: if each `f i` has degree `≤ e i`, the coefficient of the
product at `∑ e i` is the product of the top coefficients. -/
lemma coeff_prod_at_sum {ι : Type*} (s : Finset ι) (f : ι → F[X]) (e : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ e i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (f i).coeff (e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hdeg : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, e i :=
      le_trans (Polynomial.natDegree_prod_le s f)
        (Finset.sum_le_sum (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
        coeff_mul_add_eq_of_natDegree_le (h a (Finset.mem_insert_self a s)) hdeg,
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

/-- **The classical Hasse-Wronskian of distinct-degree polynomials is nonzero.** For `P : Fin l →
F[X]` nonzero with degrees `dⱼ := natDegree (P j)` distinct in `F`, `det[hasseDeriv a (P j)] ≠ 0`. -/
theorem hasseWronskian_distinctDeg_ne_zero {l : ℕ} (P : Fin l → F[X])
    (hP : ∀ j, P j ≠ 0)
    (hinj : Function.Injective (fun j => ((P j).natDegree : F))) :
    (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) (P j))).det ≠ 0 := by
  classical
  set d : Fin l → ℕ := fun j => (P j).natDegree with hd
  set D := (∑ j, d j) - ∑ a : Fin l, (a : ℕ) with hDdef
  -- per-permutation: coeff_D of the product equals (∏ C(d,σ))·(∏ lead).
  have hperm : ∀ σ : Equiv.Perm (Fin l),
      (∏ i, hasseDeriv (σ i : ℕ) (P i)).coeff D
        = (∏ i, (↑(Nat.choose (d i) (σ i)) : F)) * (∏ i, (P i).coeff (d i)) := by
    intro σ
    by_cases hbig : ∃ a, (d a : ℕ) < σ a
    · obtain ⟨a, ha⟩ := hbig
      have hz : hasseDeriv (σ a : ℕ) (P a) = 0 :=
        hasseDeriv_eq_zero_of_lt_natDegree (P a) (σ a) ha
      have hprodz : (∏ i, hasseDeriv (σ i : ℕ) (P i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) hz
      have hCz : (∏ i, (↑(Nat.choose (d i) (σ i)) : F)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a)
          (by rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero])
      rw [hprodz, Polynomial.coeff_zero, hCz, zero_mul]
    · push_neg at hbig
      have hsum : (∑ i, (d i - σ i)) = D := by
        rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => hbig i)]
        congr 1
        exact Equiv.sum_comp σ (fun a => (a : ℕ))
      have hentry : ∀ i, (hasseDeriv (σ i : ℕ) (P i)).coeff (d i - σ i)
          = (↑(Nat.choose (d i) (σ i)) : F) * (P i).coeff (d i) := by
        intro i
        rw [hasseDeriv_coeff, Nat.sub_add_cancel (hbig i)]
      rw [← hsum, coeff_prod_at_sum Finset.univ _ (fun i => d i - σ i)
        (fun i _ => le_trans (natDegree_hasseDeriv_le (P i) (σ i)) (by rw [hd]))]
      rw [Finset.prod_congr rfl (fun i _ => hentry i), ← Finset.prod_mul_distrib]
  -- coeff_D of the Wronskian = (∏ lead)·det[C(d,·)], routed through `A = brickᵀ`.
  have hcoeff : (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) (P j))).det.coeff D
      = (∏ i, (P i).coeff (d i)) * (Matrix.of (fun i a : Fin l => (Nat.choose (d i) a : F))).det := by
    have stepA : (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) (P j))).det.coeff D
        = (∏ i, (P i).coeff (d i))
            * (Matrix.of (fun x y : Fin l => (Nat.choose (d y) x : F))).det := by
      rw [Matrix.det_apply', Matrix.det_apply', Polynomial.finset_sum_coeff, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      have hentry2 : (∏ i, (Matrix.of (fun a j : Fin l => hasseDeriv (a : ℕ) (P j))) (σ i) i)
          = ∏ i, hasseDeriv (σ i : ℕ) (P i) := by
        refine Finset.prod_congr rfl (fun i _ => ?_); simp [Matrix.of_apply]
      rw [hentry2, Polynomial.coeff_intCast_mul, hperm σ]
      have hA : (∏ i, (Matrix.of (fun x y : Fin l => (Nat.choose (d y) x : F))) (σ i) i)
          = ∏ i, (↑(Nat.choose (d i) (σ i)) : F) := by
        refine Finset.prod_congr rfl (fun i _ => ?_); simp [Matrix.of_apply]
      rw [hA]; ring
    rw [stepA]
    congr 1
    have htr : (Matrix.of (fun x y : Fin l => (Nat.choose (d y) x : F)))
        = (Matrix.of (fun i a : Fin l => (Nat.choose (d i) a : F)))ᵀ := by
      ext x y; simp [Matrix.transpose_apply, Matrix.of_apply]
    rw [htr, Matrix.det_transpose]
  intro hzero
  have hlead : (∏ i, (P i).coeff (d i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [hd]; exact Polynomial.leadingCoeff_ne_zero.mpr (hP i)
  have hdet : (Matrix.of (fun i a : Fin l => (Nat.choose (d i) a : F))).det ≠ 0 :=
    det_choose_ne_zero d hinj
  exact (mul_ne_zero hlead hdet) (by rw [← hcoeff, hzero, Polynomial.coeff_zero])

end ProximityGap.BinomialDet

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.coeff_prod_at_sum
#print axioms ProximityGap.BinomialDet.hasseWronskian_distinctDeg_ne_zero
