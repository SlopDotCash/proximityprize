/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24ReducedIntersectionMatrix

/-!
# [AGL24] §3: the determinant degree bound (issue #346, brick 16)

The algebraic core of the certificate machinery's per-step probability `(t−1)k/(q−n)`
(Corollary 3.12's engine): the determinant of any square submatrix of the reduced
intersection matrix has degree at most `(fiber size)·(k−1)` in each variable `Xᵢ` — because
each RIM row mentions only its own edge's variable, to power at most `k−1`.

* `degreeOf_RIM_entry_le` / `degreeOf_RIM_entry_eq_zero` — the entry-level facts;
* `degreeOf_RIM_submatrix_det_le` — **the bound**: `degreeOf i₀ (det) ≤ |rows from edge i₀| · (k−1)`,
  via the Leibniz expansion (`det_apply'`), `degreeOf_sum_le`, `degreeOf_prod_le`, and the
  per-entry split.

Downstream, a uniformly random `αᵢ₀` over `≥ q − n` values zeroes a nonzero such determinant
with probability at most `(fiber)·(k−1)/(q−n)` — the one-variable Schwartz–Zippel step the
certificate probability (Lemma 3.11/Corollary 3.12) iterates `r` times.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- RIM entries from a row of edge `i` have `Xᵢ₀`-degree zero unless `i = i₀`. -/
theorem degreeOf_RIM_entry_eq_zero {t k : ℕ} (e : ι → Finset (Fin (t + 1)))
    (i₀ : ι) (r : RIMRowIdx e) (c : Fin t × Fin k) (hne : r.1 ≠ i₀) :
    MvPolynomial.degreeOf i₀ (RIM F e r c) = 0 := by
  obtain ⟨i, j⟩ := r
  unfold RIM
  by_cases h1 : c.1.castSucc = (e i).min' ⟨j.val, j.property.1⟩
  · rw [if_pos h1]
    exact MvPolynomial.degreeOf_X_pow_of_ne _ (Ne.symm hne)
  · rw [if_neg h1]
    by_cases h2 : c.1.castSucc = j.val
    · rw [if_pos h2]
      rw [show MvPolynomial.degreeOf i₀ (-(MvPolynomial.X i ^ (c.2.val) : MvPolynomial ι F))
          = MvPolynomial.degreeOf i₀ ((MvPolynomial.X i ^ (c.2.val) : MvPolynomial ι F)) from by
        unfold MvPolynomial.degreeOf
        rw [MvPolynomial.degrees_neg]]
      exact MvPolynomial.degreeOf_X_pow_of_ne _ (Ne.symm hne)
    · rw [if_neg h2]
      simp

/-- Every RIM entry has `Xᵢ₀`-degree at most `k − 1`. -/
theorem degreeOf_RIM_entry_le {t k : ℕ} (e : ι → Finset (Fin (t + 1)))
    (i₀ : ι) (r : RIMRowIdx e) (c : Fin t × Fin k) :
    MvPolynomial.degreeOf i₀ (RIM F e r c) ≤ k - 1 := by
  obtain ⟨i, j⟩ := r
  unfold RIM
  have hpow : MvPolynomial.degreeOf i₀ ((MvPolynomial.X i ^ (c.2.val) : MvPolynomial ι F))
      ≤ k - 1 := by
    by_cases hi : i = i₀
    · subst hi
      rw [MvPolynomial.degreeOf_X_self_pow]
      have := c.2.isLt
      omega
    · rw [MvPolynomial.degreeOf_X_pow_of_ne _ (fun h => hi h.symm)]
      exact Nat.zero_le _
  by_cases h1 : c.1.castSucc = (e i).min' ⟨j.val, j.property.1⟩
  · rw [if_pos h1]
    exact hpow
  · rw [if_neg h1]
    by_cases h2 : c.1.castSucc = j.val
    · rw [if_pos h2]
      rw [show MvPolynomial.degreeOf i₀ (-(MvPolynomial.X i ^ (c.2.val) : MvPolynomial ι F))
          = MvPolynomial.degreeOf i₀ ((MvPolynomial.X i ^ (c.2.val) : MvPolynomial ι F)) from by
        unfold MvPolynomial.degreeOf
        rw [MvPolynomial.degrees_neg]]
      exact hpow
    · rw [if_neg h2]
      simp

/-- **The determinant degree bound** ([AGL24] §3, the Corollary 3.12 engine): the determinant
of any square RIM submatrix has `Xᵢ₀`-degree at most `(number of rows from edge i₀)·(k−1)`. -/
theorem degreeOf_RIM_submatrix_det_le {t k : ℕ} (e : ι → Finset (Fin (t + 1)))
    (i₀ : ι) (rows : Fin t × Fin k → RIMRowIdx e) :
    MvPolynomial.degreeOf i₀ ((RIM F e).submatrix rows id).det
      ≤ (Finset.univ.filter (fun c => (rows c).1 = i₀)).card * (k - 1) := by
  classical
  rw [Matrix.det_apply']
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
  rw [Finset.sup_le_iff]
  intro σ _
  -- Strip the sign.
  have hsign : MvPolynomial.degreeOf i₀
      ((((Equiv.Perm.sign σ : ℤ) : MvPolynomial ι F))
        * ∏ c, ((RIM F e).submatrix rows id) (σ c) c)
      ≤ MvPolynomial.degreeOf i₀ (∏ c, ((RIM F e).submatrix rows id) (σ c) c) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs]
      push_cast
      rw [one_mul]
    · rw [hs]
      push_cast
      rw [neg_one_mul]
      unfold MvPolynomial.degreeOf
      rw [MvPolynomial.degrees_neg]
  refine le_trans hsign ?_
  refine le_trans (MvPolynomial.degreeOf_prod_le _ _ _) ?_
  -- Per-column: only the columns whose σ-row comes from edge i₀ contribute.
  calc ∑ c, MvPolynomial.degreeOf i₀ (((RIM F e).submatrix rows id) (σ c) c)
      = ∑ c ∈ Finset.univ.filter (fun c => (rows (σ c)).1 = i₀),
          MvPolynomial.degreeOf i₀ (((RIM F e).submatrix rows id) (σ c) c) := by
        rw [eq_comm]
        refine Finset.sum_filter_of_ne ?_
        intro c _ hne
        by_contra hrow
        exact hne (degreeOf_RIM_entry_eq_zero e i₀ (rows (σ c)) c hrow)
  _ ≤ ∑ _c ∈ Finset.univ.filter (fun c => (rows (σ c)).1 = i₀), (k - 1) := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact degreeOf_RIM_entry_le e i₀ (rows (σ c)) c
  _ = (Finset.univ.filter (fun c => (rows (σ c)).1 = i₀)).card * (k - 1) := by
        rw [Finset.sum_const, smul_eq_mul]
  _ = (Finset.univ.filter (fun c => (rows c).1 = i₀)).card * (k - 1) := by
        congr 1
        refine Finset.card_bij' (fun c _ => σ c) (fun c _ => σ.symm c) ?_ ?_ ?_ ?_
        · intro c hc
          rw [Finset.mem_filter] at hc ⊢
          exact ⟨Finset.mem_univ _, hc.2⟩
        · intro c hc
          rw [Finset.mem_filter] at hc ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [Equiv.apply_symm_apply]
          exact hc.2
        · intro c _
          exact σ.symm_apply_apply c
        · intro c _
          exact σ.apply_symm_apply c

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.degreeOf_RIM_entry_eq_zero
#print axioms AGL24.degreeOf_RIM_entry_le
#print axioms AGL24.degreeOf_RIM_submatrix_det_le
