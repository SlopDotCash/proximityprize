/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonResidualFloor

/-!
# The coset-word agreement cap: the full `μ_d` family (#389)

Generalizes `pm_one_agreement_le` (`d = 2`) to every root-of-unity-valued word:

> **`coset_word_agreement_le`** — for a word `w` with `w(i)^d = 1` everywhere
> (`1 ≤ d`), every codeword of `rsCode dom k` agrees with `w` on at most
> `max (d·(k−1)) (sup over v ∈ μ_d of the class size of v)` points.

Mechanism: agreement beyond `d(k−1)` forces `P^d − 1` (degree `≤ d(k−1)`) past its
root budget, so `P^d = 1`, so `P` is a constant `d`-th root of unity, and constant
agreement is a class size.  Together with `class_supply_floor`, the entire coset-word
family (`χ`-power words `x^{(q−1)/d·j}`, μ_d-valued) is now formally capped-and-
concentrating: each is admissible for `SubJohnsonSupplyResidual` whenever
`d(k−1)` and its class sizes fit under `2k+m+1`, and carries `≥ C(s_max, k+m+1)`
explainable cores.  Among coset words the `d = 2` (±1) family maximizes the class
floor (`s_max ≈ n/2`), matching the probes' extremizer; the `d > 2` family fills in
the toy-scale profile of the capped optimum.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The coset-word agreement cap** (`μ_d`-valued words, general `d ≥ 1`). -/
theorem coset_word_agreement_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {d : ℕ} (hd : 1 ≤ d) {w : Fin n → F} (hw : ∀ i, w i ^ d = 1)
    {c : Fin n → F} (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => c i = w i)).card
      ≤ max (d * (k - 1))
          (((Finset.univ : Finset F).filter (fun v => v ^ d = 1)).sup
            (fun v => ((Finset.univ : Finset (Fin n)).filter
              (fun i => w i = v)).card)) := by
  classical
  obtain ⟨P, hPdeg, rfl⟩ := hc
  set A := (Finset.univ : Finset (Fin n)).filter
    (fun i => P.eval (dom i) = w i) with hA
  by_cases hbig : A.card ≤ d * (k - 1)
  · exact le_trans hbig (le_max_left _ _)
  push_neg at hbig
  rcases eq_or_ne P 0 with rfl | hP0
  · -- the zero codeword never agrees with a root-of-unity-valued word
    have hempty : A = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
      have hval := (Finset.mem_filter.mp hi).2
      have h1 := hw i
      rw [← hval] at h1
      simp only [Polynomial.eval_zero] at h1
      rw [zero_pow (by omega : d ≠ 0)] at h1
      exact zero_ne_one h1
    rw [hempty, Finset.card_empty] at hbig
    omega
  -- P^d − 1 vanishes on A beyond its degree
  have hPnat : P.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
  have hQdeg : (P ^ d - 1 : F[X]).natDegree ≤ d * (k - 1) := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · rw [Polynomial.natDegree_pow]
      exact Nat.mul_le_mul_left _ (by omega)
    · simp
  have hQ : (P ^ d - 1 : F[X]) = 0 := by
    by_contra hQ0
    have hroots : ∀ i ∈ A, (P ^ d - 1 : F[X]).eval (dom i) = 0 := by
      intro i hi
      have hval := (Finset.mem_filter.mp hi).2
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one, hval, hw i,
        sub_self]
    have := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (f := (P ^ d - 1 : F[X])) (s := A.image dom) ?_ ?_
    · exact hQ0 this
    · rw [Finset.card_image_of_injective _ dom.injective]
      calc (P ^ d - 1 : F[X]).degree ≤ ((P ^ d - 1 : F[X]).natDegree : WithBot ℕ) :=
            Polynomial.degree_le_natDegree
      _ ≤ ((d * (k - 1) : ℕ) : WithBot ℕ) := by exact_mod_cast hQdeg
      _ < (A.card : WithBot ℕ) := by exact_mod_cast hbig
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hroots i hi
  -- P^d = 1 ⟹ P is a constant d-th root of unity
  have hPd : P ^ d = 1 := by linear_combination hQ
  have hPnat0 : P.natDegree = 0 := by
    have h := congrArg Polynomial.natDegree hPd
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_one] at h
    rcases Nat.mul_eq_zero.mp h with h1 | h1
    · omega
    · exact h1
  have hv : (P.coeff 0) ^ d = 1 := by
    have h := congrArg (Polynomial.eval (0 : F)) hPd
    rw [Polynomial.eval_pow, Polynomial.eval_one] at h
    rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hle1 : ((Finset.univ : Finset (Fin n)).filter (fun i => w i = P.coeff 0)).card
      ≤ ((Finset.univ : Finset F).filter (fun v => v ^ d = 1)).sup
          (fun v => ((Finset.univ : Finset (Fin n)).filter (fun i => w i = v)).card) :=
    Finset.le_sup (f := fun v => ((Finset.univ : Finset (Fin n)).filter
      (fun i => w i = v)).card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
  refine le_trans (Finset.card_le_card ?_) (le_trans hle1 (le_max_right _ _))
  intro i hi
  have hival := (Finset.mem_filter.mp hi).2
  have hPC : P = Polynomial.C (P.coeff 0) :=
    Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hPnat0)
  rw [hPC, Polynomial.eval_C] at hival
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hival.symm⟩

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.coset_word_agreement_le
