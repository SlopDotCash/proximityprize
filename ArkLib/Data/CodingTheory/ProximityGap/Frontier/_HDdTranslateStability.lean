/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (standalone issue #1)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HDdNodeTranslation
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# HDd — translation stability of downward-closed monomial spans

Every exponent vector `ν` in the support of `translateD d α y (monomial μ c)` has
`ν 0 ≤ μ 0`, `ν 1 ≤ μ 1`, and `ν (t+2) = μ (t+2)` at every derivative coordinate
(`support_translateD_monomial`); hence the translated monomial lies in the span of the
monomials with lowered `(a, b₀)` exponents (`translateD_monomial_mem_span`).  A monomial
family that is downward closed in `(a, b₀)` — as every probe cap space is, since the
weighted degree only drops — therefore spans a `translateD`-stable subspace; combined with
`contactSubstD_translate` and `originNodeFamily_rank_le_blockCount`, the node maps at
EVERY `(α, y)` have restricted rank at most the origin block count.  This closes the last
named (non-bookkeeping) step of the certificate chain.

Proof route: a uniform `degreeOf` bound gives the two `≤`'s; weighted homogeneity with a
coordinate-indicator weight gives the derivative-coordinate equalities.
-/

namespace ArkLib.ProximityGap.Frontier.HD1Contact

open Submodule MvPolynomial

variable {F : Type*} [CommRing F]

theorem translateD_C (d : ℕ) (α y c : F) : translateD d α y (C c) = C c := by
  simp [translateD, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-! ## Derivative coordinates are exact (indicator-weight homogeneity) -/

/-- Indicator weight of one derivative coordinate. -/
def coordW (d : ℕ) (t : Fin d) : Fin (d + 2) → ℕ :=
  fun i => if i = t.succ.succ then 1 else 0

theorem weight_coordW {d : ℕ} (t : Fin d) (ν : Fin (d + 2) →₀ ℕ) :
    Finsupp.weight (coordW d t) ν = ν t.succ.succ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_single t.succ.succ]
  · simp [coordW]
  · intro i _ hne
    simp [coordW, hne]
  · intro hns
    simp [Finsupp.notMem_support_iff.mp hns]

theorem coordW_zero {d : ℕ} (t : Fin d) : coordW d t 0 = 0 := by
  have h : (0 : Fin (d + 2)) ≠ t.succ.succ := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_succ] at this
  simp [coordW, h]

theorem coordW_one {d : ℕ} (t : Fin d) : coordW d t 1 = 0 := by
  have h : (1 : Fin (d + 2)) ≠ t.succ.succ := by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_succ, Fin.val_one] at this
  simp [coordW, h]

theorem translateD_X_coord_homogeneous (d : ℕ) (α y : F) (t : Fin d) (i : Fin (d + 2)) :
    IsWeightedHomogeneous (coordW d t) (translateD d α y (X i)) (coordW d t i) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · simp only [translateD, aeval_X, Fin.cons_zero, coordW_zero]
    have hX : IsWeightedHomogeneous (coordW d t)
        (X (0 : Fin (d + 2)) : MvPolynomial _ F) 0 := by
      have h := isWeightedHomogeneous_X F (coordW d t) (0 : Fin (d + 2))
      rwa [coordW_zero] at h
    exact hX.add (isWeightedHomogeneous_C _ _)
  · have h1 : (Fin.succ 0 : Fin (d + 2)) = 1 := by ext; simp
    simp only [translateD, aeval_X, Fin.cons_succ, Fin.cons_zero, h1, coordW_one]
    have hX : IsWeightedHomogeneous (coordW d t)
        (X (1 : Fin (d + 2)) : MvPolynomial _ F) 0 := by
      have h := isWeightedHomogeneous_X F (coordW d t) (1 : Fin (d + 2))
      rwa [coordW_one] at h
    exact hX.add (isWeightedHomogeneous_C _ _)
  · simp only [translateD, aeval_X, Fin.cons_succ]
    exact isWeightedHomogeneous_X F (coordW d t) j.succ.succ

theorem translateD_monomial_coord_homogeneous (d : ℕ) (α y : F) (t : Fin d)
    (μ : Fin (d + 2) →₀ ℕ) (c : F) :
    IsWeightedHomogeneous (coordW d t) (translateD d α y (monomial μ c))
      (μ t.succ.succ) := by
  classical
  rw [show (monomial μ c : MvPolynomial (Fin (d + 2)) F) =
      C c * μ.prod fun i k => X i ^ k from monomial_eq, map_mul]
  have hC : IsWeightedHomogeneous (coordW d t) (translateD d α y (C c)) 0 := by
    rw [translateD_C]
    exact isWeightedHomogeneous_C _ _
  have hdeg : (μ t.succ.succ : ℕ) = μ.sum fun i k => k • coordW d t i := by
    have h := weight_coordW t μ
    rw [Finsupp.weight_apply] at h
    exact h.symm
  rw [hdeg]
  have hprod : IsWeightedHomogeneous (coordW d t)
      (translateD d α y (μ.prod fun i k => X i ^ k))
      (μ.sum fun i k => k • coordW d t i) := by
    rw [Finsupp.prod, map_prod, Finsupp.sum]
    exact IsWeightedHomogeneous.prod _ _ _ fun i _ => by
      rw [map_pow]
      exact (translateD_X_coord_homogeneous d α y t i).pow _
  simpa using hC.mul hprod

/-! ## The `(a, b₀)` coordinates only drop (uniform `degreeOf` bound) -/

theorem degreeOf_translateD_X_le [Nontrivial F] (d : ℕ) (α y : F)
    (i₀ i : Fin (d + 2)) :
    degreeOf i₀ (translateD d α y (X i)) ≤ if i₀ = i then 1 else 0 := by
  classical
  have hbound : ∀ (i' : Fin (d + 2)) (e : F),
      degreeOf i₀ ((X i' + C e : MvPolynomial (Fin (d + 2)) F)) ≤
      if i₀ = i' then 1 else 0 := by
    intro i' e
    refine (degreeOf_add_le _ _ _).trans ?_
    rcases eq_or_ne i₀ i' with rfl | hne
    · simp [degreeOf_X_self, degreeOf_C]
    · simp [degreeOf_X_of_ne hne, degreeOf_C]
  refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun j => ?_) i') i
  · simpa [translateD, aeval_X, Fin.cons_zero] using hbound 0 α
  · simp only [translateD, aeval_X, Fin.cons_succ, Fin.cons_zero]
    have h1 : (Fin.succ 0 : Fin (d + 2)) = 1 := by ext; simp
    rw [h1]
    exact hbound 1 y
  · simp only [translateD, aeval_X, Fin.cons_succ]
    rcases eq_or_ne i₀ j.succ.succ with rfl | hne
    · simp [degreeOf_X_self]
    · simp [degreeOf_X_of_ne hne]

theorem degreeOf_translateD_monomial_le [Nontrivial F] (d : ℕ) (α y : F)
    (μ : Fin (d + 2) →₀ ℕ) (c : F) (i₀ : Fin (d + 2)) :
    degreeOf i₀ (translateD d α y (monomial μ c)) ≤ μ i₀ := by
  classical
  rw [show (monomial μ c : MvPolynomial (Fin (d + 2)) F) =
      C c * μ.prod fun i k => X i ^ k from monomial_eq, map_mul]
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [translateD_C, degreeOf_C, zero_add, Finsupp.prod, map_prod]
  refine (degreeOf_prod_le _ _ _).trans ?_
  have hterm : ∀ i ∈ μ.support,
      degreeOf i₀ (translateD d α y (X i ^ μ i)) ≤ if i₀ = i then μ i else 0 := by
    intro i _
    rw [map_pow]
    refine (degreeOf_pow_le _ _ _).trans ?_
    have := degreeOf_translateD_X_le (F := F) d α y i₀ i
    rcases eq_or_ne i₀ i with rfl | hne
    · simp only [if_pos rfl] at this ⊢
      calc μ i₀ * degreeOf i₀ (translateD d α y (X i₀)) ≤ μ i₀ * 1 :=
            Nat.mul_le_mul_left _ this
        _ = μ i₀ := Nat.mul_one _
    · simp only [if_neg hne] at this ⊢
      simpa [Nat.le_zero] using Nat.mul_le_mul_left (μ i) this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite_eq μ.support i₀ (fun i => μ i)]
  split_ifs with h
  · exact le_rfl
  · exact Nat.zero_le _

/-! ## The support bound and span stability -/

/-- **Support bound.**  Exponent vectors in the support of a translated monomial have
lowered `(a, b₀)` exponents and identical derivative exponents. -/
theorem support_translateD_monomial [Nontrivial F] (d : ℕ) (α y : F)
    (μ : Fin (d + 2) →₀ ℕ) (c : F) (ν : Fin (d + 2) →₀ ℕ)
    (hν : ν ∈ (translateD d α y (monomial μ c)).support) :
    ν 0 ≤ μ 0 ∧ ν 1 ≤ μ 1 ∧ ∀ t : Fin d, ν t.succ.succ = μ t.succ.succ := by
  refine ⟨?_, ?_, ?_⟩
  · have h := degreeOf_translateD_monomial_le d α y μ c 0
    rw [degreeOf_eq_sup] at h
    exact le_trans (Finset.le_sup (f := fun m : Fin (d + 2) →₀ ℕ => m 0) hν) h
  · have h := degreeOf_translateD_monomial_le d α y μ c 1
    rw [degreeOf_eq_sup] at h
    exact le_trans (Finset.le_sup (f := fun m : Fin (d + 2) →₀ ℕ => m 1) hν) h
  · intro t
    have h := translateD_monomial_coord_homogeneous d α y t μ c
      (mem_support_iff.mp hν)
    rwa [weight_coordW] at h

/-- **Span stability.**  The translation maps a monomial into the span of the monomials
with lowered `(a, b₀)` exponents and the same derivative exponents. -/
theorem translateD_monomial_mem_span [Nontrivial F] (d : ℕ) (α y : F)
    (μ : Fin (d + 2) →₀ ℕ) (c : F) :
    translateD d α y (monomial μ c) ∈
      span F ((fun ν => (monomial ν (1 : F) : MvPolynomial (Fin (d + 2)) F)) ''
        {ν | ν 0 ≤ μ 0 ∧ ν 1 ≤ μ 1 ∧ ∀ t : Fin d, ν t.succ.succ = μ t.succ.succ}) := by
  classical
  rw [as_sum (translateD d α y (monomial μ c))]
  refine sum_mem fun ν hν => ?_
  rw [show (monomial ν (coeff ν (translateD d α y (monomial μ c))) :
      MvPolynomial (Fin (d + 2)) F) =
      (coeff ν (translateD d α y (monomial μ c))) • monomial ν (1 : F) from by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  exact smul_mem _ _ (subset_span
    ⟨ν, support_translateD_monomial d α y μ c ν hν, rfl⟩)

end ArkLib.ProximityGap.Frontier.HD1Contact

#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.translateD_monomial_mem_span
#print axioms ArkLib.ProximityGap.Frontier.HD1Contact.support_translateD_monomial
