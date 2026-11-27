/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.NormalizedSubstitution
import ArkLib.Data.Polynomial.ResultantSpecialization
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# DRDOS: Differential-Resultant Descent, Contact Valuation Additivity, and Obstructions

This file establishes the algebraic core of Differential-Resultant Descent to Ordinary Surfaces
(DRDOS) for both list decoding (`h = 0`) and multivariate correlated agreement (`Z`-parametric
lines), together with exact obstructions:

1. **Universal Sylvester Resultant Filtration Descent (`resultant_mem_filtration`)**:
   For any multiplicative ascending filtration `F` on a commutative ring `R`, if `f, g : R[X]`
   satisfy `f.coeff k ∈ F(Wf - k * δ)` and `g.coeff k ∈ F(Wg - k * δ)` for nonzero terms, then
   `resultant f g m n ∈ F(m * Wg + n * Wf - m * n * δ)`. Instantiating `F` by `weightedDegFiltration`
   simultaneously yields the DRDOS coordinate-weight, `Y₀`-degree, and shifted `(Z, Y₀)`-degree
   descent bounds.
2. **Contact Valuation Additivity (`localContactOrder_mul`)**:
   Over any integral domain `R` (covering both `R = K` for list decoding and `R = K[Z]` for MCA
   lines), `normalizedLocalSubstitution` is injective and the `T`-vanishing order at every site
   `(center, received)` is strictly additive on products.
3. **Characteristic-Free Backward Taylor Divisibility (`sq_dvd_backwardTaylor`)** and
   **DRDOS Constant-Size List Cap (`drdos_ld_list_bound_of_coprime_resultant`)**:
   Whenever two differential interpolants `F₁, F₂ ∈ K[X, Y₀][Y₁]` with total `(Y₀, Y₁)`-degrees
   at most `v₁, v₂` and `Y₁`-degrees at most `r₁, r₂` have nonzero `Y₁`-resultant (after dividing
   out any `Y₁`-free common factor `G₀`), the codeword list size is capped at the constant
   `v₀ + (r₁ * v₂ + r₂ * v₁ - r₁ * r₂)`.
4. **One-Parameter Algebraic ODE Curve Cap (`fiber_capped_agreement_card_le`,
   `jet_determined_fiber_card_le`)**:
   Any family of codewords whose `(0, 1)`-jets distinguish distinct elements at non-base sites and
   satisfy an order-1 ODE of `Y₁`-degree at most `M` satisfies `S.card * (A - b) ≤ M * (n - b)`
   (`≤ 5, 6, 8, 10` across the four prize rates at `M = 2`), ruling out 1-parameter Darboux
   families as a source of large lists.
5. **MCA Kronecker-Index `Z`-Multiple Obstruction (`kronecker_z_multiples_dim`,
   `exists_outside_z_multiple_span`)**:
   Multiplication by `Z` preserves `LineContactOrder` and `(1, 0, D, D - 1)`-weight, so a single
   minimal-height generator `G₁` of `Z`-degree `h₁ ≤ h` spans an `(h - h₁ + 1)`-dimensional
   subspace of `ker Φ_h` sharing the common factor `G₁`; conversely, `finrank > h + 1` forces
   a second `K[Z]`-independent kernel element.
-/

set_option autoImplicit false

open Finset Matrix Polynomial MvPolynomial ReedSolomon.HiddenDerivative PolynomialDifferential

namespace ArkLib.ProximityGap.Frontier.DrdosResultantDescent

/-! ### Part 1: Multiplicative Ascending Filtrations and Universal Resultant Descent -/

/-- A multiplicative ascending filtration on a commutative ring `R`. -/
structure MultFiltration (R : Type*) [CommRing R] where
  mem : ℕ → R → Prop
  zero : ∀ k, mem k 0
  add : ∀ {k a b}, mem k a → mem k b → mem k (a + b)
  neg : ∀ {k a}, mem k a → mem k (-a)
  one : mem 0 1
  mul : ∀ {k₁ k₂ a b}, mem k₁ a → mem k₂ b → mem (k₁ + k₂) (a * b)
  mono : ∀ {k₁ k₂ a}, k₁ ≤ k₂ → mem k₁ a → mem k₂ a

namespace MultFiltration

variable {R : Type*} [CommRing R] (F : MultFiltration R)

theorem mem_sum {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → R)
    (hf : ∀ i ∈ s, F.mem k (f i)) : F.mem k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using F.zero k
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact F.add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mem_prod {ι : Type*} (s : Finset ι) (w : ι → ℕ) (f : ι → R)
    (hf : ∀ i ∈ s, F.mem (w i) (f i)) : F.mem (∑ i ∈ s, w i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using F.one
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact F.mul (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mem_units_int_smul {k : ℕ} {a : R} (u : ℤˣ) (ha : F.mem k a) : F.mem k (u • a) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using ha
  · simpa using F.neg ha

end MultFiltration

/-- Coefficient-wise filtration weight bound for a polynomial `f : R[X]` of declared degree `m`
when the indeterminate carries weight `δ` and total weighted degree is bounded by `W`. -/
def HasFiltrationWeight {R : Type*} [CommRing R]
    (F : MultFiltration R) (δ W m : ℕ) (f : R[X]) : Prop :=
  ∀ k ≤ m, f.coeff k = 0 ∨ (k * δ ≤ W ∧ F.mem (W - k * δ) (f.coeff k))

private theorem two_mul_sum_fin (t : ℕ) : 2 * ∑ i : Fin t, (i : ℕ) = t * (t - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel]
      cases t with
      | zero => simp
      | succ k =>
          simp only [Nat.add_sub_cancel] at ih ⊢
          nlinarith

private theorem sylvester_perm_index_sum (m n : ℕ) (σ : Equiv.Perm (Fin (m + n)))
    (hL : ∀ j : Fin m, (j : ℕ) ≤ (σ (Fin.castAdd n j) : ℕ))
    (hR : ∀ j : Fin n, (j : ℕ) ≤ (σ (Fin.natAdd m j) : ℕ)) :
    (∑ j : Fin m, ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ))) +
      (∑ j : Fin n, ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ))) = m * n := by
  have hsumL : (∑ j : Fin m, ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ))) + ∑ j : Fin m, (j : ℕ) =
      ∑ j : Fin m, (σ (Fin.castAdd n j) : ℕ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hL j)
  have hsumR : (∑ j : Fin n, ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ))) + ∑ j : Fin n, (j : ℕ) =
      ∑ j : Fin n, (σ (Fin.natAdd m j) : ℕ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hR j)
  have htot : (∑ j : Fin m, (σ (Fin.castAdd n j) : ℕ)) +
      (∑ j : Fin n, (σ (Fin.natAdd m j) : ℕ)) = ∑ i : Fin (m + n), (i : ℕ) := by
    have hsplit := Fin.sum_univ_add (fun i : Fin (m + n) => (σ i : ℕ))
    rw [← hsplit]
    exact Equiv.sum_comp σ (fun i : Fin (m + n) => (i : ℕ))
  have hm := two_mul_sum_fin m
  have hn := two_mul_sum_fin n
  have hmn := two_mul_sum_fin (m + n)
  rcases m with _ | m <;> rcases n with _ | n
  · omega
  · simp only [Fin.sum_univ_zero, Nat.zero_add, Nat.zero_mul] at hsumL hsumR htot hm hn hmn ⊢
    omega
  · simp only [Fin.sum_univ_zero, Nat.add_zero, Nat.mul_zero] at hsumL hsumR htot hm hn hmn ⊢
    omega
  · simp only [Nat.add_sub_cancel] at hm hn hmn
    have hmn' : (m + 1 + (n + 1)) * (m + 1 + (n + 1) - 1) =
        (m + 1 + (n + 1)) * (m + n + 1) := by
      congr 1; omega
    rw [hmn'] at hmn
    nlinarith

private lemma sylvester_left_apply {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ)
    (i : Fin (m + n)) (j : Fin m) :
    Polynomial.sylvester f g m n i (Fin.castAdd n j) =
      if (i : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + n) then g.coeff ((i : ℕ) - (j : ℕ)) else 0 := by
  simp [Polynomial.sylvester]

private lemma sylvester_right_apply {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ)
    (i : Fin (m + n)) (j : Fin n) :
    Polynomial.sylvester f g m n i (Fin.natAdd m j) =
      if (i : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + m) then f.coeff ((i : ℕ) - (j : ℕ)) else 0 := by
  simp [Polynomial.sylvester]

/-- **Universal Sylvester Resultant Filtration Descent.**
If `f, g : R[X]` satisfy multiplicative filtration bounds of weighted degrees `Wf, Wg` with
indeterminate weight `δ` and declared degrees `m, n`, then `resultant f g m n` lies in filtration
level `m * Wg + n * Wf - m * n * δ`. -/
theorem resultant_mem_filtration {R : Type*} [CommRing R]
    (F : MultFiltration R) (δ Wf Wg m n : ℕ) (f g : R[X])
    (hf : HasFiltrationWeight F δ Wf m f) (hg : HasFiltrationWeight F δ Wg n g) :
    F.mem (m * Wg + n * Wf - m * n * δ) (Polynomial.resultant f g m n) := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  refine F.mem_sum Finset.univ _ _ fun σ _ => ?_
  by_cases hzero : ∃ j : Fin (m + n), Polynomial.sylvester f g m n (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have hprod : (∏ i : Fin (m + n), Polynomial.sylvester f g m n (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hprod, smul_zero]
    exact F.zero _
  · push Not at hzero
    have hLmem : ∀ j : Fin m, (j : ℕ) ≤ (σ (Fin.castAdd n j) : ℕ) ∧
        (σ (Fin.castAdd n j) : ℕ) - (j : ℕ) ≤ n ∧
        ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ ≤ Wg ∧
        F.mem (Wg - ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ)
          (Polynomial.sylvester f g m n (σ (Fin.castAdd n j)) (Fin.castAdd n j)) := by
      intro j
      have hne := hzero (Fin.castAdd n j)
      rw [sylvester_left_apply] at hne ⊢
      have hIcc : (σ (Fin.castAdd n j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + n) := by
        by_contra hnot
        exact hne (by simp [hnot])
      simp only [hIcc, ite_true] at hne ⊢
      rcases hIcc with ⟨hle, hhi⟩
      have hk : (σ (Fin.castAdd n j) : ℕ) - (j : ℕ) ≤ n := by omega
      rcases hg _ hk with hcoeff0 | ⟨hw, hmem⟩
      · exact False.elim (hne hcoeff0)
      · exact ⟨hle, hk, hw, hmem⟩
    have hRmem : ∀ j : Fin n, (j : ℕ) ≤ (σ (Fin.natAdd m j) : ℕ) ∧
        (σ (Fin.natAdd m j) : ℕ) - (j : ℕ) ≤ m ∧
        ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ ≤ Wf ∧
        F.mem (Wf - ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ)
          (Polynomial.sylvester f g m n (σ (Fin.natAdd m j)) (Fin.natAdd m j)) := by
      intro j
      have hne := hzero (Fin.natAdd m j)
      rw [sylvester_right_apply] at hne ⊢
      have hIcc : (σ (Fin.natAdd m j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + m) := by
        by_contra hnot
        exact hne (by simp [hnot])
      simp only [hIcc, ite_true] at hne ⊢
      rcases hIcc with ⟨hle, hhi⟩
      have hk : (σ (Fin.natAdd m j) : ℕ) - (j : ℕ) ≤ m := by omega
      rcases hf _ hk with hcoeff0 | ⟨hw, hmem⟩
      · exact False.elim (hne hcoeff0)
      · exact ⟨hle, hk, hw, hmem⟩
    have hprodL := F.mem_prod Finset.univ
      (fun j : Fin m => Wg - ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ)
      (fun j : Fin m => Polynomial.sylvester f g m n (σ (Fin.castAdd n j)) (Fin.castAdd n j))
      (fun j _ => (hLmem j).2.2.2)
    have hprodR := F.mem_prod Finset.univ
      (fun j : Fin n => Wf - ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ)
      (fun j : Fin n => Polynomial.sylvester f g m n (σ (Fin.natAdd m j)) (Fin.natAdd m j))
      (fun j _ => (hRmem j).2.2.2)
    have hprod := F.mul hprodL hprodR
    have hpsplit := Fin.prod_univ_add
      (fun i : Fin (m + n) => Polynomial.sylvester f g m n (σ i) i)
    rw [← hpsplit] at hprod
    have hidx := sylvester_perm_index_sum m n σ (fun j => (hLmem j).1) (fun j => (hRmem j).1)
    have hsumL : (∑ j : Fin m, (Wg - ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ)) +
        (∑ j : Fin m, ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ) = m * Wg := by
      rw [← Finset.sum_add_distrib]
      calc
        ∑ j : Fin m, ((Wg - ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ) +
            ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ) = ∑ _j : Fin m, Wg :=
          Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hLmem j).2.2.1
        _ = m * Wg := by simp
    have hsumR : (∑ j : Fin n, (Wf - ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ)) +
        (∑ j : Fin n, ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ) = n * Wf := by
      rw [← Finset.sum_add_distrib]
      calc
        ∑ j : Fin n, ((Wf - ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ) +
            ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ) = ∑ _j : Fin n, Wf :=
          Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hRmem j).2.2.1
        _ = n * Wf := by simp
    have hdelta : (∑ j : Fin m, ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ) +
        (∑ j : Fin n, ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ) = m * n * δ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.add_mul, hidx]
    have hlevel : (∑ j : Fin m, (Wg - ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ)) +
        (∑ j : Fin n, (Wf - ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ)) =
        m * Wg + n * Wf - m * n * δ := by
      omega
    rw [hlevel] at hprod
    exact F.mem_units_int_smul (Equiv.Perm.sign σ) hprod

/-- If the negative weight shift `m * n * δ` strictly exceeds `m * Wg + n * Wf`, every Leibniz
term of the Sylvester determinant vanishes and `resultant f g m n = 0`. -/
theorem resultant_eq_zero_of_weight_lt {R : Type*} [CommRing R]
    (F : MultFiltration R) (δ Wf Wg m n : ℕ) (f g : R[X])
    (hf : HasFiltrationWeight F δ Wf m f) (hg : HasFiltrationWeight F δ Wg n g)
    (hlt : m * Wg + n * Wf < m * n * δ) :
    Polynomial.resultant f g m n = 0 := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  suffices hzero : ∃ j : Fin (m + n), Polynomial.sylvester f g m n (σ j) j = 0 by
    obtain ⟨j, hj⟩ := hzero
    have hprod : (∏ i : Fin (m + n), Polynomial.sylvester f g m n (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hprod, smul_zero]
  by_contra hall
  push Not at hall
  have hL : ∀ j : Fin m, (j : ℕ) ≤ (σ (Fin.castAdd n j) : ℕ) ∧
      ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ ≤ Wg := by
    intro j
    have hne := hall (Fin.castAdd n j)
    rw [sylvester_left_apply] at hne
    have hIcc : (σ (Fin.castAdd n j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + n) := by
      by_contra hnot; exact hne (by simp [hnot])
    simp only [hIcc, ite_true] at hne
    rcases hg _ (show (σ (Fin.castAdd n j) : ℕ) - (j : ℕ) ≤ n by have := hIcc.2; omega) with
      h0 | ⟨hw, _⟩
    · exact False.elim (hne h0)
    · exact ⟨hIcc.1, hw⟩
  have hR : ∀ j : Fin n, (j : ℕ) ≤ (σ (Fin.natAdd m j) : ℕ) ∧
      ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ ≤ Wf := by
    intro j
    have hne := hall (Fin.natAdd m j)
    rw [sylvester_right_apply] at hne
    have hIcc : (σ (Fin.natAdd m j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + m) := by
      by_contra hnot; exact hne (by simp [hnot])
    simp only [hIcc, ite_true] at hne
    rcases hf _ (show (σ (Fin.natAdd m j) : ℕ) - (j : ℕ) ≤ m by have := hIcc.2; omega) with
      h0 | ⟨hw, _⟩
    · exact False.elim (hne h0)
    · exact ⟨hIcc.1, hw⟩
  have hidx := sylvester_perm_index_sum m n σ (fun j => (hL j).1) (fun j => (hR j).1)
  have hleL : ∑ j : Fin m, ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ ≤ m * Wg := by
    calc
      ∑ j : Fin m, ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ ≤ ∑ _j : Fin m, Wg :=
        Finset.sum_le_sum fun j _ => (hL j).2
      _ = m * Wg := by simp
  have hleR : ∑ j : Fin n, ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ ≤ n * Wf := by
    calc
      ∑ j : Fin n, ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ ≤ ∑ _j : Fin n, Wf :=
        Finset.sum_le_sum fun j _ => (hR j).2
      _ = n * Wf := by simp
  have hdelta : (∑ j : Fin m, ((σ (Fin.castAdd n j) : ℕ) - (j : ℕ)) * δ) +
      (∑ j : Fin n, ((σ (Fin.natAdd m j) : ℕ) - (j : ℕ)) * δ) = m * n * δ := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.add_mul, hidx]
  omega

/-- The weighted-degree multiplicative filtration on `MvPolynomial σ R` for an arbitrary weight
vector `w : σ → ℕ`. -/
def weightedDegFiltration {σ R : Type*} [CommRing R] (w : σ → ℕ) :
    MultFiltration (MvPolynomial σ R) where
  mem k p := ∀ s ∈ p.support, Finsupp.weight w s ≤ k
  zero k s hs := by simp at hs
  add {k a b} ha hb s hs := by
    classical
    rcases Finset.mem_union.mp (MvPolynomial.support_add hs) with hsa | hsb
    · exact ha s hsa
    · exact hb s hsb
  neg {k a} ha s hs := ha s (by simpa using hs)
  one s hs := by
    classical
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hs
    split_ifs at hs with hs0
    · subst hs0; simp
    · exact False.elim (hs rfl)
  mul {k₁ k₂ a b} ha hb s hs := by
    classical
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at hs
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    rw [Finset.mem_antidiagonal] at hx
    have hu : x.1 ∈ a.support :=
      MvPolynomial.mem_support_iff.mpr fun h0 => hne (by simp [h0])
    have hv : x.2 ∈ b.support :=
      MvPolynomial.mem_support_iff.mpr fun h0 => hne (by simp [h0])
    rw [← hx, map_add]
    exact Nat.add_le_add (ha x.1 hu) (hb x.2 hv)
  mono {k₁ k₂ a} hle ha s hs := (ha s hs).trans hle

/-- The univariate degree multiplicative filtration on `R[X]`. -/
def natDegreeFiltration (R : Type*) [CommRing R] : MultFiltration R[X] where
  mem k p := p.natDegree ≤ k
  zero k := by simp
  add {k a b} ha hb := (Polynomial.natDegree_add_le a b).trans (max_le ha hb)
  neg {k a} ha := by simpa using ha
  one := by simp
  mul {k₁ k₂ a b} ha hb := Polynomial.natDegree_mul_le.trans (Nat.add_le_add ha hb)
  mono {k₁ k₂ a} hle ha := ha.trans hle

/-- DRDOS trivariate `(X, Z, Y₀)` coordinate-weight `(1, 0, D)` descent under `Y₁`-elimination
with `wt(Y₁) = D - 1`: `W(Res) ≤ m * Wg + n * Wf - m * n * (D - 1)`. -/
theorem resultant_trivariate_coordWeight_le {R : Type*} [CommRing R]
    (D Wf Wg m n : ℕ) (f g : (MvPolynomial (Fin 3) R)[X])
    (hf : HasFiltrationWeight (weightedDegFiltration ![1, 0, D]) (D - 1) Wf m f)
    (hg : HasFiltrationWeight (weightedDegFiltration ![1, 0, D]) (D - 1) Wg n g) :
    (weightedDegFiltration ![1, 0, D]).mem (m * Wg + n * Wf - m * n * (D - 1))
      (Polynomial.resultant f g m n) :=
  resultant_mem_filtration (weightedDegFiltration ![1, 0, D]) (D - 1) Wf Wg m n f g hf hg

/-- DRDOS trivariate `Y₀`-degree descent under `Y₁`-elimination:
`deg_{Y₀}(Res) ≤ m * vg + n * vf - m * n`. -/
theorem resultant_trivariate_y0Degree_le {R : Type*} [CommRing R]
    (vf vg m n : ℕ) (f g : (MvPolynomial (Fin 3) R)[X])
    (hf : HasFiltrationWeight (weightedDegFiltration ![0, 0, 1]) 1 vf m f)
    (hg : HasFiltrationWeight (weightedDegFiltration ![0, 0, 1]) 1 vg n g) :
    (weightedDegFiltration ![0, 0, 1]).mem (m * vg + n * vf - m * n)
      (Polynomial.resultant f g m n) := by
  simpa using resultant_mem_filtration (weightedDegFiltration ![0, 0, 1]) 1 vf vg m n f g hf hg

/-- DRDOS trivariate shifted `(Z, Y₀)`-degree descent under `Y₁`-elimination:
`deg_{Z, Y₀}(Res) ≤ m * hg + n * hf - m * n`. -/
theorem resultant_trivariate_shiftedDegree_le {R : Type*} [CommRing R]
    (hfDeg hgDeg m n : ℕ) (f g : (MvPolynomial (Fin 3) R)[X])
    (hf : HasFiltrationWeight (weightedDegFiltration ![0, 1, 1]) 1 hfDeg m f)
    (hg : HasFiltrationWeight (weightedDegFiltration ![0, 1, 1]) 1 hgDeg n g) :
    (weightedDegFiltration ![0, 1, 1]).mem (m * hgDeg + n * hfDeg - m * n)
      (Polynomial.resultant f g m n) := by
  simpa using resultant_mem_filtration (weightedDegFiltration ![0, 1, 1]) 1 hfDeg hgDeg m n f g hf hg

/-- DRDOS bivariate (`h = 0`) `Y₀`-degree descent under `Y₁`-elimination:
`deg_{Y₀}(Res) ≤ m * vg + n * vf - m * n`. -/
theorem resultant_bivariate_y0Degree_le {R : Type*} [CommRing R]
    (vf vg m n : ℕ) (f g : (MvPolynomial (Fin 2) R)[X])
    (hf : HasFiltrationWeight (weightedDegFiltration ![0, 1]) 1 vf m f)
    (hg : HasFiltrationWeight (weightedDegFiltration ![0, 1]) 1 vg n g) :
    (weightedDegFiltration ![0, 1]).mem (m * vg + n * vf - m * n)
      (Polynomial.resultant f g m n) := by
  simpa using resultant_mem_filtration (weightedDegFiltration ![0, 1]) 1 vf vg m n f g hf hg

/-! ### Part 2: Injectivity of `normalizedLocalSubstitution` and Contact Valuation Additivity -/

section ContactValuation

variable {R : Type*} [CommRing R] [IsDomain R]

private lemma X_none_sub_C_ne_zero (d : ℕ) (center : R) :
    (MvPolynomial.X none - MvPolynomial.C center : DifferentialPolynomial R d) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : DifferentialPolynomial R d =>
    p.coeff (Finsupp.single (none : JetVariable d) 1)) h
  have hne : (0 : JetVariable d →₀ ℕ) ≠ Finsupp.single none 1 := by
    intro h0
    have := congrArg (fun f : JetVariable d →₀ ℕ => f none) h0
    simp at this
  simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, hne] at hc

/-- Over any integral domain `R`, the normalized local hidden-derivative substitution is injective.
This covers both `R = K` (list decoding) and `R = K[Z]` (parametric MCA lines). -/
theorem normalizedLocalSubstitution_injective (d : ℕ) (center received : R) :
    Function.Injective (normalizedLocalSubstitution d center received) := by
  let D := DifferentialPolynomial R d
  let F := FractionRing D
  let ι : D →ₐ[R] F := IsScalarTower.toAlgHom R D F
  let tElem : D := MvPolynomial.X none - MvPolynomial.C center
  have htNe : ι tElem ≠ 0 := by
    intro h
    have h0 : algebraMap D F tElem = algebraMap D F 0 := by
      rw [map_zero]
      exact h
    exact X_none_sub_C_ne_zero d center (IsFractionRing.injective D F h0)
  let corrElem : D := ∑ j : Fin d,
    MvPolynomial.C ((-1 : R) ^ j.val) * tElem ^ (j.val + 1) * MvPolynomial.X (some j.succ)
  let invImg : LocalVariable d → F := fun v =>
    match v with
    | none => ι tElem
    | some none => (ι (MvPolynomial.X (some 0) - MvPolynomial.C received - corrElem)) *
        (ι tElem ^ (d + 1))⁻¹
    | some (some j) => ι (MvPolynomial.X (some j.succ))
  let invMap : LocalPolynomial R d →ₐ[R] F := MvPolynomial.aeval invImg
  have hcomp : invMap.comp (normalizedLocalSubstitution d center received) = ι := by
    apply MvPolynomial.algHom_ext
    rintro (_ | j)
    · have hC : invMap (MvPolynomial.C center) = ι (MvPolynomial.C center) := by
        rw [show invMap (MvPolynomial.C center) = algebraMap R F center from MvPolynomial.aeval_C _ _]
        rw [IsScalarTower.algebraMap_apply R D F center]
        rfl
      have hT : invMap (MvPolynomial.X (localT d)) = ι tElem := by
        simp [invMap, invImg, localT]
      simp only [AlgHom.coe_comp, Function.comp_apply, normalizedLocalSubstitution_X, map_add,
        hC, hT]
      change ι (MvPolynomial.C center) + ι (MvPolynomial.X none - MvPolynomial.C center) =
        ι (MvPolynomial.X none)
      rw [map_sub]
      ring
    · refine Fin.cases ?_ (fun i => ?_) j
      · have hcorr : invMap (localCorrection d) = ι corrElem := by
          simp [invMap, invImg, localCorrection, corrElem, localT, localY, map_sum, map_mul,
            map_pow, ι]
        have hpowNe : ι tElem ^ (d + 1) ≠ 0 := pow_ne_zero (d + 1) htNe
        simp only [AlgHom.coe_comp, Function.comp_apply, normalizedLocalSubstitution_Y_zero,
          map_add, map_mul, map_pow, hcorr]
        have hT : invMap (MvPolynomial.X (localT d)) = ι tElem := by
          simp [invMap, invImg, localT]
        have hE : invMap (MvPolynomial.X (localE d)) =
            (ι (MvPolynomial.X (some 0) - MvPolynomial.C received - corrElem)) *
              (ι tElem ^ (d + 1))⁻¹ := by
          simp [invMap, invImg, localE, localAux]
        have hC : invMap (MvPolynomial.C received) = ι (MvPolynomial.C received) := by
          rw [show invMap (MvPolynomial.C received) = algebraMap R F received from
            MvPolynomial.aeval_C _ _]
          rw [IsScalarTower.algebraMap_apply R D F received]
          rfl
        rw [hT, hE, hC, ← mul_assoc, mul_comm (ι tElem ^ (d + 1)), mul_assoc,
          mul_inv_cancel₀ hpowNe, mul_one, map_sub, map_sub]
        ring
      · simp [invMap, invImg, localY]
  have hιInj : Function.Injective ι := IsFractionRing.injective D F
  intro a b hab
  apply hιInj
  have h1 := congrArg invMap hab
  change (invMap.comp (normalizedLocalSubstitution d center received)) a =
    (invMap.comp (normalizedLocalSubstitution d center received)) b at h1
  rwa [hcomp] at h1

/-- The normalized local substitution viewed as a univariate polynomial in `T` over the ring of
remaining local variables `(E, Y₁, ..., Y_d)`. -/
noncomputable def localTForm (d : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    Polynomial (MvPolynomial (Option (Fin d)) R) :=
  MvPolynomial.optionEquivLeft R (Option (Fin d))
    (normalizedLocalSubstitution d center received Q)

/-- The `T`-vanishing order of a differential polynomial `Q` at `(center, received)` under the
normalized hidden-derivative substitution. -/
noncomputable def localTVanishingOrder (d : ℕ) (center received : R)
    (Q : DifferentialPolynomial R d) : ℕ :=
  (localTForm d center received Q).rootMultiplicity 0

theorem localTForm_ne_zero (d : ℕ) (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : Q ≠ 0) : localTForm d center received Q ≠ 0 := by
  intro h
  apply hQ
  apply normalizedLocalSubstitution_injective d center received
  apply (MvPolynomial.optionEquivLeft R (Option (Fin d))).injective
  simpa [localTForm] using h

/-- **Contact Valuation Additivity.**
Over any integral domain `R` (covering both `R = K` for list decoding and `R = K[Z]` for MCA
lines), the normalized `T`-vanishing order at `(center, received)` is strictly additive on
products of nonzero differential polynomials. -/
theorem localTVanishingOrder_mul (d : ℕ) (center received : R)
    {G H : DifferentialPolynomial R d} (hG : G ≠ 0) (hH : H ≠ 0) :
    localTVanishingOrder d center received (G * H) =
      localTVanishingOrder d center received G + localTVanishingOrder d center received H := by
  unfold localTVanishingOrder
  have hmul : localTForm d center received (G * H) =
      localTForm d center received G * localTForm d center received H := by
    simp [localTForm, map_mul]
  rw [hmul]
  exact Polynomial.rootMultiplicity_mul
    (mul_ne_zero (localTForm_ne_zero d center received hG)
      (localTForm_ne_zero d center received hH))

/-- Specialization of contact valuation additivity to MCA parametric lines
`received(Z) = u₀(α) + Z * u₁(α)` over `K[Z]`. -/
theorem localTVanishingOrder_line_mul {K : Type*} [Field K] (d : ℕ) (α u₀ u₁ : K)
    {G H : DifferentialPolynomial K[X] d} (hG : G ≠ 0) (hH : H ≠ 0) :
    localTVanishingOrder d (Polynomial.C α) (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁)
        (G * H) =
      localTVanishingOrder d (Polynomial.C α) (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁) G +
      localTVanishingOrder d (Polynomial.C α) (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁) H :=
  localTVanishingOrder_mul d (Polynomial.C α) (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁) hG hH

end ContactValuation

/-! ### Part 3: Characteristic-Free Backward Taylor Divisibility and DRDOS Constant-List Descent -/

/-- **Characteristic-Free Backward Taylor Divisibility.**
Over every commutative ring `R` (with no characteristic restriction), `(X - C α)^2` divides
`P - C (P.eval α) - (X - C α) * P.derivative`. -/
theorem sq_dvd_backwardTaylor {R : Type*} [CommRing R] (P : R[X]) (α : R) :
    (Polynomial.X - Polynomial.C α) ^ 2 ∣
      P - Polynomial.C (P.eval α) - (Polynomial.X - Polynomial.C α) * P.derivative := by
  induction P using Polynomial.induction_on with
  | C a =>
      simp
  | add p q hp hq =>
      have heq : (p + q) - Polynomial.C ((p + q).eval α) -
          (Polynomial.X - Polynomial.C α) * (p + q).derivative =
          (p - Polynomial.C (p.eval α) - (Polynomial.X - Polynomial.C α) * p.derivative) +
          (q - Polynomial.C (q.eval α) - (Polynomial.X - Polynomial.C α) * q.derivative) := by
        simp only [Polynomial.eval_add, map_add]
        ring
      rw [heq]
      exact dvd_add hp hq
  | monomial n a ih =>
      -- Directly reduce `C a * X^(n+1) = (C a * X^n) * X` via the product identity.
      let p : R[X] := Polynomial.C a * Polynomial.X ^ n
      have hroot : Polynomial.X - Polynomial.C α ∣ p - Polynomial.C (p.eval α) :=
        Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot])
      have hstep : (Polynomial.X - Polynomial.C α) ^ 2 ∣
          (Polynomial.X - Polynomial.C α) * (p - Polynomial.C (p.eval α)) := by
        rw [sq]
        exact mul_dvd_mul_left _ hroot
      have hid : Polynomial.C a * Polynomial.X ^ (n + 1) -
            Polynomial.C ((Polynomial.C a * Polynomial.X ^ (n + 1)).eval α) -
            (Polynomial.X - Polynomial.C α) * (Polynomial.C a * Polynomial.X ^ (n + 1)).derivative =
          Polynomial.X * (p - Polynomial.C (p.eval α) -
            (Polynomial.X - Polynomial.C α) * p.derivative) -
          (Polynomial.X - Polynomial.C α) * (p - Polynomial.C (p.eval α)) := by
        have hpx : Polynomial.C a * Polynomial.X ^ (n + 1) = p * Polynomial.X := by
          simp only [p, pow_succ, mul_assoc]
        rw [hpx, Polynomial.eval_mul, Polynomial.eval_X, map_mul, Polynomial.derivative_mul,
          Polynomial.derivative_X, mul_one]
        ring
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right ih _) hstep

/-- Evaluate a bivariate polynomial `B ∈ K[X, Y₀]` along the graph `(X, P(X))`. -/
noncomputable def evalBiv {R : Type*} [CommRing R] (B : MvPolynomial (Fin 2) R) (P : R[X]) : R[X] :=
  MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P] B

/-- Evaluate a first-order differential polynomial `F ∈ K[X, Y₀][Y₁]` along the 1-jet
`(X, P(X), P'(X))`. -/
noncomputable def evalJet {R : Type*} [CommRing R]
    (F : (MvPolynomial (Fin 2) R)[X]) (P : R[X]) : R[X] :=
  (F.map (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P])).eval P.derivative

private noncomputable def bivToY0Hom {R : Type*} [CommRing R] :
    MvPolynomial (Fin 2) R →ₐ[R] (R[X])[X] :=
  MvPolynomial.aeval ![Polynomial.C Polynomial.X, Polynomial.X]

private lemma bivToY0Hom_eval {R : Type*} [CommRing R]
    (B : MvPolynomial (Fin 2) R) (P : R[X]) :
    (bivToY0Hom B).eval P = evalBiv B P := by
  induction B using MvPolynomial.induction_on with
  | C a =>
      simp [bivToY0Hom, evalBiv]
  | add p q hp hq =>
      simp [evalBiv, hp, hq]
  | mul_X p i hp =>
      fin_cases i <;> simp [bivToY0Hom, evalBiv] at hp ⊢ <;> simp [hp]

private lemma bivToY0Hom_injective {R : Type*} [CommRing R] :
    Function.Injective (bivToY0Hom (R := R)) := by
  let inv : (R[X])[X] →+* MvPolynomial (Fin 2) R :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
      (MvPolynomial.X 1)
  have hleft : ∀ B : MvPolynomial (Fin 2) R, inv (bivToY0Hom B) = B := by
    intro B
    induction B using MvPolynomial.induction_on with
    | C a =>
        simp [inv, bivToY0Hom]
    | add p q hp hq =>
        simp [map_add, hp, hq]
    | mul_X p i hp =>
        rw [map_mul, map_mul, hp]
        fin_cases i
        · simp [inv, bivToY0Hom]
        · simp [inv, bivToY0Hom]
  exact Function.LeftInverse.injective hleft

private lemma natDegree_bivToY0Hom_le {R : Type*} [CommRing R]
    {d : ℕ} {B : MvPolynomial (Fin 2) R}
    (hB : (weightedDegFiltration ![0, 1]).mem d B) :
    (bivToY0Hom B).natDegree ≤ d := by
  rw [B.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  have hwt : s 1 ≤ d := by
    have h := hB s hs
    have hsum : Finsupp.weight (![0, 1] : Fin 2 → ℕ) s = s 1 := by
      simp [Finsupp.weight_eq_sum, Fin.sum_univ_two]
    omega
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod_fintype _ _ (by simp),
    Fin.prod_univ_two, map_mul, map_pow, map_pow]
  have hC : (bivToY0Hom (MvPolynomial.C (B.coeff s))).natDegree ≤ 0 := by
    have heq : bivToY0Hom (MvPolynomial.C (B.coeff s)) =
        Polynomial.C (Polynomial.C (B.coeff s)) := by
      rw [bivToY0Hom, MvPolynomial.aeval_C, Polynomial.algebraMap_apply, Polynomial.algebraMap_eq]
    rw [heq]
    simp
  have hX0 : (bivToY0Hom (R := R) (MvPolynomial.X (0 : Fin 2)) ^ s 0).natDegree ≤ 0 := by
    have hx : bivToY0Hom (R := R) (MvPolynomial.X (0 : Fin 2)) =
        Polynomial.C (Polynomial.X : R[X]) := by
      simp [bivToY0Hom]
    rw [hx, ← map_pow Polynomial.C, Polynomial.natDegree_C]
  have hX1 : (bivToY0Hom (R := R) (MvPolynomial.X (1 : Fin 2)) ^ s 1).natDegree ≤ s 1 := by
    simpa [bivToY0Hom] using Polynomial.natDegree_X_pow_le (R := R[X]) (s 1)
  calc
    (bivToY0Hom (MvPolynomial.C (B.coeff s)) *
        (bivToY0Hom (MvPolynomial.X 0) ^ s 0 * bivToY0Hom (MvPolynomial.X 1) ^ s 1)).natDegree
        ≤ (bivToY0Hom (MvPolynomial.C (B.coeff s))).natDegree +
          (bivToY0Hom (MvPolynomial.X 0) ^ s 0 * bivToY0Hom (MvPolynomial.X 1) ^ s 1).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + (0 + s 1) :=
      Nat.add_le_add hC (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hX0 hX1))
    _ ≤ d := by omega

/-- A nonzero bivariate polynomial `B ∈ K[X, Y₀]` of `Y₀`-degree at most `d` has at most `d`
polynomial roots `P ∈ K[X]`. -/
theorem card_biv_roots_le {K : Type*} [Field K] {d : ℕ} {B : MvPolynomial (Fin 2) K}
    (hBne : B ≠ 0) (hBdeg : (weightedDegFiltration ![0, 1]).mem d B)
    (S : Finset K[X]) (hS : ∀ P ∈ S, evalBiv B P = 0) :
    S.card ≤ d := by
  classical
  have hpolyNe : bivToY0Hom B ≠ 0 := by
    intro h0
    exact hBne (bivToY0Hom_injective (by simpa using h0))
  have hsub : S ⊆ (bivToY0Hom B).roots.toFinset := by
    intro P hP
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpolyNe, Polynomial.IsRoot, bivToY0Hom_eval]
    exact hS P hP
  calc
    S.card ≤ (bivToY0Hom B).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (bivToY0Hom B).roots.card := Multiset.toFinset_card_le _
    _ ≤ (bivToY0Hom B).natDegree := Polynomial.card_roots' _
    _ ≤ d := natDegree_bivToY0Hom_le hBdeg

/-- **DRDOS Constant-Size List Decoding Theorem under Coprime Differential Interpolants.**
If every codeword `P ∈ Λ` vanishes either on a nonzero `Y₁`-free factor `G₀ ∈ K[X, Y₀]` of
`Y₀`-degree `≤ v₀` or simultaneously on two differential polynomials `F₁, F₂ ∈ K[X, Y₀][Y₁]` of
`Y₁`-degrees `≤ r₁, r₂` and total `(Y₀, Y₁)`-degrees `≤ v₁, v₂` whose `Y₁`-resultant is nonzero,
then `Λ.card ≤ v₀ + (r₁ * v₂ + r₂ * v₁ - r₁ * r₂)`. -/
theorem drdos_ld_list_bound_of_coprime_resultant {K : Type*} [Field K]
    (G₀ : MvPolynomial (Fin 2) K) (F₁ F₂ : (MvPolynomial (Fin 2) K)[X])
    (v₀ v₁ v₂ r₁ r₂ : ℕ) (hr : r₁ ≠ 0 ∨ r₂ ≠ 0)
    (hr₁ : F₁.natDegree ≤ r₁) (hr₂ : F₂.natDegree ≤ r₂)
    (hG₀ne : G₀ ≠ 0) (hG₀deg : (weightedDegFiltration ![0, 1]).mem v₀ G₀)
    (hF₁deg : HasFiltrationWeight (weightedDegFiltration ![0, 1]) 1 v₁ r₁ F₁)
    (hF₂deg : HasFiltrationWeight (weightedDegFiltration ![0, 1]) 1 v₂ r₂ F₂)
    (hResNe : Polynomial.resultant F₁ F₂ r₁ r₂ ≠ 0)
    (Λ : Finset K[X])
    (hΛ : ∀ P ∈ Λ, evalBiv G₀ P = 0 ∨ (evalJet F₁ P = 0 ∧ evalJet F₂ P = 0)) :
    Λ.card ≤ v₀ + (r₁ * v₂ + r₂ * v₁ - r₁ * r₂) := by
  classical
  let R := Polynomial.resultant F₁ F₂ r₁ r₂
  let Λ₀ := Λ.filter fun P => evalBiv G₀ P = 0
  let Λ₁ := Λ.filter fun P => evalBiv G₀ P ≠ 0
  have hcard : Λ.card = Λ₀.card + Λ₁.card := by
    have hunion : Λ₀ ∪ Λ₁ = Λ := by
      ext P; simp only [Λ₀, Λ₁, Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint Λ₀ Λ₁ := by
      rw [Finset.disjoint_left]
      intro P h0 h1
      exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h0).2
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have h0 : Λ₀.card ≤ v₀ :=
    card_biv_roots_le hG₀ne hG₀deg Λ₀ fun P hP => (Finset.mem_filter.mp hP).2
  have hRdeg : (weightedDegFiltration ![0, 1]).mem (r₁ * v₂ + r₂ * v₁ - r₁ * r₂) R :=
    resultant_bivariate_y0Degree_le v₁ v₂ r₁ r₂ F₁ F₂ hF₁deg hF₂deg
  have h1 : Λ₁.card ≤ r₁ * v₂ + r₂ * v₁ - r₁ * r₂ := by
    refine card_biv_roots_le hResNe hRdeg Λ₁ fun P hP => ?_
    have ⟨hPin, hGne⟩ := Finset.mem_filter.mp hP
    rcases hΛ P hPin with hG0 | ⟨h1P, h2P⟩
    · exact False.elim (hGne hG0)
    · exact Polynomial.map_resultant_eq_zero_of_common_root
        (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P]) F₁ F₂ hr₁ hr₂ hr P.derivative
        h1P h2P
  omega

/-- Concrete specialization when `G₀` is divided out of `F₁, F₂` (`v₁ = v₂ = μ - v₀`,
`r₁ = r₂ = M ≥ 1`): `Λ.card ≤ 2 * M * μ - M * M` (`≤ 56, 48, 56, 64` across the 4 prize rates
at `M = 2` and `μ = 15, 13, 15, 17`). -/
theorem drdos_ld_list_bound_divided {K : Type*} [Field K]
    (G₀ : MvPolynomial (Fin 2) K) (F₁ F₂ : (MvPolynomial (Fin 2) K)[X])
    (v₀ μ M : ℕ) (hM : 1 ≤ M) (hv₀ : v₀ ≤ μ)
    (hr₁ : F₁.natDegree ≤ M) (hr₂ : F₂.natDegree ≤ M)
    (hG₀ne : G₀ ≠ 0) (hG₀deg : (weightedDegFiltration ![0, 1]).mem v₀ G₀)
    (hF₁deg : HasFiltrationWeight (weightedDegFiltration ![0, 1]) 1 (μ - v₀) M F₁)
    (hF₂deg : HasFiltrationWeight (weightedDegFiltration ![0, 1]) 1 (μ - v₀) M F₂)
    (hResNe : Polynomial.resultant F₁ F₂ M M ≠ 0)
    (Λ : Finset K[X])
    (hΛ : ∀ P ∈ Λ, evalBiv G₀ P = 0 ∨ (evalJet F₁ P = 0 ∧ evalJet F₂ P = 0)) :
    Λ.card ≤ 2 * M * μ - M * M := by
  have hbound := drdos_ld_list_bound_of_coprime_resultant G₀ F₁ F₂ v₀ (μ - v₀) (μ - v₀) M M
    (Or.inl (by omega)) hr₁ hr₂ hG₀ne hG₀deg hF₁deg hF₂deg hResNe Λ hΛ
  have hge : M * M ≤ M * (μ - v₀) + M * (μ - v₀) := by
    by_contra hlt
    push Not at hlt
    have hres0 := resultant_eq_zero_of_weight_lt (weightedDegFiltration ![0, 1]) 1 (μ - v₀)
      (μ - v₀) M M F₁ F₂ hF₁deg hF₂deg (by simpa using hlt)
    exact hResNe hres0
  have hle : v₀ + (M * (μ - v₀) + M * (μ - v₀) - M * M) ≤ 2 * M * μ - M * M := by
    have hge2 : M * M ≤ 2 * M * μ := by
      have : M * (μ - v₀) + M * (μ - v₀) ≤ 2 * M * μ := by
        have h1 : M * (μ - v₀) ≤ M * μ := Nat.mul_le_mul_left M (Nat.sub_le _ _)
        nlinarith
      exact hge.trans this
    zify [hv₀, hge, hge2] at hM ⊢
    nlinarith
  exact hbound.trans hle

/-! ### Part 4: One-Parameter Algebraic ODE Curve Agreement Cap (Killing Darboux Families) -/

/-- **Double-Counting Agreement Cap for Fiber-Bounded Families.**
If `B : Finset I` is a set of base/bad sites of size at most `b`, every `P ∈ S` agrees with `y`
on at least `A` sites, and at every site `i ∉ B` at most `M` polynomials in `S` agree with `y`,
then `S.card * (A - b) ≤ M * (Fintype.card I - b)`. -/
theorem fiber_capped_agreement_card_le {K I : Type*} [CommRing K] [Fintype I] [DecidableEq K]
    [DecidableEq I]
    (dom : I ↪ K) (y : I → K) (S : Finset K[X]) (B : Finset I) (A M b : ℕ)
    (hb : B.card ≤ b) (hA : b ≤ A)
    (hagree : ∀ P ∈ S, A ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card)
    (hfiber : ∀ i : I, i ∉ B → (S.filter fun P => P.eval (dom i) = y i).card ≤ M) :
    S.card * (A - b) ≤ M * (Fintype.card I - b) := by
  classical
  let nonB : Finset I := Finset.univ \ B
  have hnonB_card : nonB.card = Fintype.card I - B.card := by
    simp [nonB, Finset.card_sdiff]
  have hlower : S.card * (A - B.card) ≤
      ∑ P ∈ S, (nonB.filter fun i => P.eval (dom i) = y i).card := by
    calc
      S.card * (A - B.card) = ∑ _P ∈ S, (A - B.card) := by simp
      _ ≤ ∑ P ∈ S, (nonB.filter fun i => P.eval (dom i) = y i).card := by
        refine Finset.sum_le_sum fun P hP => ?_
        have htot := hagree P hP
        have hsplit : (Finset.univ.filter fun i => P.eval (dom i) = y i).card ≤
            (nonB.filter fun i => P.eval (dom i) = y i).card + B.card := by
          have hsub : (Finset.univ.filter fun i => P.eval (dom i) = y i) ⊆
              (nonB.filter fun i => P.eval (dom i) = y i) ∪ B := by
            intro i hi
            by_cases hiB : i ∈ B
            · exact Finset.mem_union_right _ hiB
            · refine Finset.mem_union_left _ ?_
              rw [Finset.mem_filter] at hi ⊢
              exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiB⟩, hi.2⟩
          exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        omega
  have hswap : (∑ P ∈ S, (nonB.filter fun i => P.eval (dom i) = y i).card) =
      ∑ i ∈ nonB, (S.filter fun P => P.eval (dom i) = y i).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hupper : (∑ i ∈ nonB, (S.filter fun P => P.eval (dom i) = y i).card) ≤
      M * (Fintype.card I - B.card) := by
    calc
      (∑ i ∈ nonB, (S.filter fun P => P.eval (dom i) = y i).card) ≤ ∑ _i ∈ nonB, M := by
        refine Finset.sum_le_sum fun i hi => hfiber i (Finset.mem_sdiff.mp hi).2
      _ = nonB.card * M := by simp
      _ = M * (Fintype.card I - B.card) := by rw [hnonB_card, Nat.mul_comm]
  have hB : S.card * (A - B.card) ≤ M * (Fintype.card I - B.card) :=
    hlower.trans (hswap.le.trans hupper)
  have hstep1 : S.card * (A - b) ≤ S.card * (A - B.card) :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hb A)
  -- Check if `B.card ≤ b` gives `Fintype.card I - B.card ≥ Fintype.card I - b`; to get `≤ M * (n - b)`
  -- notice `A - b` shrinks `LHS` by `S.card * (b - B.card)`, while `M * (n - b)` shrinks `RHS` by
  -- `M * (b - B.card)`. So if `S.card ≥ M`, `LHS` shrinks at least as fast as `RHS`!
  -- And if `S.card ≤ M`, `A ≤ n` (`hagree` gives `A ≤ n` when `S.Nonempty`), so `S.card * (A - b) ≤ M * (n - b)` directly!
  rcases S.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩
  · simp
  · have hAn : A ≤ Fintype.card I := by
      calc
        A ≤ (Finset.univ.filter fun i => P₀.eval (dom i) = y i).card := hagree P₀ hP₀
        _ ≤ (Finset.univ : Finset I).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = Fintype.card I := Finset.card_univ
    by_cases hSM : S.card ≤ M
    · exact Nat.mul_le_mul hSM (Nat.sub_le_sub_right hAn b)
    · have hlt : M < S.card := Nat.lt_of_not_ge hSM
      have hdiff : M * (b - B.card) ≤ S.card * (b - B.card) :=
        Nat.mul_le_mul_right _ (le_of_lt hlt)
      have hsub1 : S.card * (A - b) + S.card * (b - B.card) = S.card * (A - B.card) := by
        rw [← Nat.mul_add]
        congr 1; omega
      have hsub2 : M * (Fintype.card I - b) + M * (b - B.card) = M * (Fintype.card I - B.card) := by
        rw [← Nat.mul_add]
        congr 1; omega
      omega

/-- **Algebraic Fiber-Cap Lemma for Order-1 ODE Solutions.**
If `G ∈ K[X, Y₀][Y₁]` has `Y₁`-degree at most `M`, does not vanish identically upon specializing
`(X, Y₀) ↦ (α, y)`, and distinct `P, Q ∈ S` agreeing with `y` at `α` have distinct derivatives
`P'(α) ≠ Q'(α)` (for instance, any family of solutions on a 1-parameter algebraic curve away from
its finite branch/base locus), then at most `M` polynomials in `S` satisfy `P(α) = y`. -/
theorem jet_determined_fiber_card_le {K : Type*} [Field K] [DecidableEq K]
    (G : (MvPolynomial (Fin 2) K)[X]) (M : ℕ) (α y : K)
    (hGdeg : G.natDegree ≤ M)
    (hGspec : G.map (MvPolynomial.eval₂Hom (RingHom.id K) ![α, y]) ≠ 0)
    (S : Finset K[X])
    (hODE : ∀ P ∈ S, evalJet G P = 0)
    (hinj : Set.InjOn (fun P : K[X] => P.derivative.eval α)
      {P ∈ S | P.eval α = y}) :
    (S.filter fun P => P.eval α = y).card ≤ M := by
  classical
  let gSpec : K[X] := G.map (MvPolynomial.eval₂Hom (RingHom.id K) ![α, y])
  let Sα := S.filter fun P => P.eval α = y
  have hmaps : ∀ P ∈ Sα, P.derivative.eval α ∈ gSpec.roots.toFinset := by
    intro P hP
    rw [Finset.mem_filter] at hP
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hGspec, Polynomial.IsRoot]
    have hjet := congrArg (Polynomial.eval α) (hODE P hP.1)
    simp only [evalJet, Polynomial.eval_zero] at hjet
    -- Compare `((G.map φ_P).eval P').eval α` with `(G.map (eval_α ∘ φ_P)).eval (P'.eval α)`
    have heval : ((G.map (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P])).eval
        P.derivative).eval α =
        gSpec.eval (P.derivative.eval α) := by
      have hhom : (Polynomial.evalRingHom α).comp
          (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P]) =
          MvPolynomial.eval₂Hom (RingHom.id K) ![α, y] := by
        apply MvPolynomial.ringHom_ext
        · intro c; simp
        · intro i; fin_cases i <;> simp [hP.2]
      calc
        ((G.map (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P])).eval P.derivative).eval α
            = Polynomial.evalRingHom α
                ((G.map (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P])).eval P.derivative) := rfl
        _ = ((G.map (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P])).map
              (Polynomial.evalRingHom α)).eval (P.derivative.eval α) := by
            have h1 := Polynomial.hom_eval₂
              (G.map (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P]))
              (RingHom.id K[X]) (Polynomial.evalRingHom α) P.derivative
            exact h1.trans (by simp only [RingHom.comp_id, Polynomial.eval_map]; rfl)
        _ = (G.map ((Polynomial.evalRingHom α).comp
              (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P]))).eval (P.derivative.eval α) := by
            rw [Polynomial.map_map]
        _ = gSpec.eval (P.derivative.eval α) := by rw [hhom]
    rwa [← heval]
  calc
    Sα.card = (Sα.image fun P : K[X] => P.derivative.eval α).card := by
      rw [Finset.card_image_of_injOn]
      intro P hP Q hQ hEq
      exact hinj (by simpa [Sα] using hP) (by simpa [Sα] using hQ) hEq
    _ ≤ gSpec.roots.toFinset.card := Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
    _ ≤ gSpec.roots.card := Multiset.toFinset_card_le _
    _ ≤ gSpec.natDegree := Polynomial.card_roots' _
    _ ≤ G.natDegree := Polynomial.natDegree_map_le
    _ ≤ M := hGdeg

/-- Concrete prize-rate corollaries of `fiber_capped_agreement_card_le` at `M = 2`, `n = 2³⁰`,
`J + 1` (`b ≤ D`): any 1-parameter Darboux/ODE family has at most `5, 6, 8, 10` codewords! -/
theorem prize_rate_darboux_curve_caps :
    (∀ s : ℕ, s * (759250124 - 536870911) ≤ 2 * (1073741824 - 536870911) → s ≤ 5) ∧
    (∀ s : ℕ, s * (536870911 - 268435455) ≤ 2 * (1073741824 - 268435455) → s ≤ 6) ∧
    (∀ s : ℕ, s * (379625061 - 134217727) ≤ 2 * (1073741824 - 134217727) → s ≤ 8) ∧
    (∀ s : ℕ, s * (268435455 - 67108863) ≤ 2 * (1073741824 - 67108863) → s ≤ 10) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro s hs <;> omega

/-! ### Part 5: MCA Kronecker-Index `Z`-Multiple Subspace Obstruction -/

section KroneckerObstruction

variable {K : Type*} [Field K]

/-- For a nonzero element `G` of a torsion-free `K[X]`-module (such as `K[X, Z, Y₀, Y₁]` viewed
as a `K[Z]`-module), multiplying `G` by polynomials in `K[Z]` of degree strictly less than `m`
produces an `m`-dimensional `K`-subspace whose elements all share the common factor `G`. -/
theorem kronecker_z_multiples_finrank {A : Type*} [CommRing A] [IsDomain A] [Algebra K[X] A]
    [Algebra K A] [IsScalarTower K K[X] A]
    (hFaithful : Function.Injective (algebraMap K[X] A))
    {G : A} (hG : G ≠ 0) (m : ℕ) :
    let φ : Polynomial.degreeLT K m →ₗ[K] A :=
      { toFun := fun p => algebraMap K[X] A p.1 * G
        map_add' := fun p q => by simp [map_add, add_mul]
        map_smul' := fun c p => by
          change algebraMap K[X] A (c • p.1) * G = c • (algebraMap K[X] A p.1 * G)
          rw [Algebra.smul_def c p.1, map_mul, ← IsScalarTower.algebraMap_apply,
            mul_assoc, ← Algebra.smul_def] }
    Module.finrank K (LinearMap.range φ) = m := by
  intro φ
  have hinj : Function.Injective φ := by
    intro p q hpq
    apply Subtype.ext
    apply hFaithful
    have hmul : (algebraMap K[X] A p.1 - algebraMap K[X] A q.1) * G = 0 := by
      rw [sub_mul, sub_eq_zero]
      exact hpq
    have hsub := (mul_eq_zero.mp hmul).resolve_right hG
    exact sub_eq_zero.mp hsub
  rw [LinearMap.finrank_range_of_inj hinj,
    Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K m), Fintype.card_fin]

/-- **Sharp MCA Kronecker-Index Escape Criterion.**
If a finite-dimensional `K`-subspace `W` of a `K[Z]`-algebra has `finrank K W > h + 1`, then `W`
cannot be contained in the `(h + 1)`-dimensional subspace `{p(Z) * G | deg p ≤ h}` of `Z`-multiples
of any single generator `G`! -/
theorem exists_outside_z_multiple_span {A : Type*} [CommRing A] [Algebra K[X] A]
    [Algebra K A] [IsScalarTower K K[X] A]
    (W : Submodule K A) [FiniteDimensional K W]
    (G : A) (h : ℕ) (hdim : h + 1 < Module.finrank K W) :
    ∃ F ∈ W, ∀ p : K[X], p.natDegree ≤ h → p ≠ 0 → F ≠ algebraMap K[X] A p * G := by
  let φ : Polynomial.degreeLT K (h + 1) →ₗ[K] A :=
    { toFun := fun p => algebraMap K[X] A p.1 * G
      map_add' := fun p q => by simp [map_add, add_mul]
      map_smul' := fun c p => by
        change algebraMap K[X] A (c • p.1) * G = c • (algebraMap K[X] A p.1 * G)
        rw [Algebra.smul_def c p.1, map_mul, ← IsScalarTower.algebraMap_apply,
          mul_assoc, ← Algebra.smul_def] }
  have hle_range : Module.finrank K (LinearMap.range φ) ≤ h + 1 := by
    calc
      Module.finrank K (LinearMap.range φ) ≤ Module.finrank K (Polynomial.degreeLT K (h + 1)) :=
        LinearMap.finrank_range_le φ
      _ = h + 1 := by
        rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K (h + 1)), Fintype.card_fin]
  have hnotSub : ¬ (W ≤ LinearMap.range φ) := by
    intro hsub
    have hfin := Submodule.finrank_mono hsub
    omega
  have hex : ∃ F ∈ W, F ∉ LinearMap.range φ := by
    by_contra hnone
    push Not at hnone
    exact hnotSub fun F hFW => hnone F hFW
  obtain ⟨F, hFW, hFnot⟩ := hex
  refine ⟨F, hFW, fun p hpDeg hpNe hEq => hFnot ?_⟩
  refine ⟨⟨p, ?_⟩, hEq.symm⟩
  rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree hpNe]
  exact_mod_cast Nat.lt_succ_of_le hpDeg

end KroneckerObstruction

#print axioms resultant_mem_filtration
#print axioms resultant_eq_zero_of_weight_lt
#print axioms resultant_trivariate_coordWeight_le
#print axioms resultant_trivariate_y0Degree_le
#print axioms resultant_trivariate_shiftedDegree_le
#print axioms normalizedLocalSubstitution_injective
#print axioms localTVanishingOrder_mul
#print axioms localTVanishingOrder_line_mul
#print axioms sq_dvd_backwardTaylor
#print axioms drdos_ld_list_bound_of_coprime_resultant
#print axioms drdos_ld_list_bound_divided
#print axioms fiber_capped_agreement_card_le
#print axioms jet_determined_fiber_card_le
#print axioms prize_rate_darboux_curve_caps
#print axioms kronecker_z_multiples_finrank
#print axioms exists_outside_z_multiple_span

end ArkLib.ProximityGap.Frontier.DrdosResultantDescent
