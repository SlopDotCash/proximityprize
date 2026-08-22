/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.AgreementCount
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# HeavyCodeword

Module docstring for `HeavyCodeword.lean`.
-/


open Polynomial Finset BigOperators
open scoped NNReal

namespace ProximityGap

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Coefficient extraction for the per-coordinate curve polynomial. -/
private lemma sumMonomial_coeff {k : ℕ} (a : Fin (k + 1) → F) (t : Fin (k + 1)) :
    (∑ t' : Fin (k + 1), Polynomial.monomial (t' : ℕ) (a t')).coeff (t : ℕ) = a t := by
  classical
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single t
      (fun b _ hb => if_neg (fun h => hb (Fin.val_injective h)))
      (fun h => absurd (Finset.mem_univ t) h)]
  simp

/-- **Heavy codeword ⟹ joint agreement.** If strictly more than `k · |ι|` curve parameters
agree with a codeword `c ∈ C` on `≥ |ι| - e` coordinates (and `0 ∈ C`, `k < |F|`), then the word
stack `u` jointly agrees with `C` at radius `δ` (provided `e` matches `δ`: `(1-δ)|ι| ≤ |ι|-e`).

This is the BCIKS dichotomy made concrete: a heavily-hit codeword forces the curve to be
*permanently* `c` (so `u 0 = c`, `u t = 0` for `t ≥ 1`) on a `≥ |ι| - e`-size set, which is
exactly joint agreement with the codewords `(c, 0, …, 0)`. It connects the agreement-count bound
to the proximity-gap conclusion. -/
theorem jointAgreement_of_heavy_codeword {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (u : Fin (k + 1) → ι → F) (c : ι → F) (e : ℕ)
    (hk : k < Fintype.card F)
    (hc : c ∈ C) (h0 : (0 : ι → F) ∈ C)
    (hsize : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ ((Fintype.card ι - e : ℕ) : ℝ≥0))
    (hheavy : k * Fintype.card ι <
      (Finset.univ.filter (fun z : F =>
        Fintype.card ι - e ≤
          (Finset.univ.filter
            (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card)).card) :
    Code.jointAgreement (κ := Fin (k + 1)) C δ u := by
  classical
  have hA := permanentAgreement_of_card_curveAgreement_gt u c e hheavy
  set A : Finset ι :=
    Finset.univ.filter (fun i => ∀ z : F, ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i) with hAdef
  -- structure on A: `u 0 = c` and `u t = 0` for `t ≠ 0`
  have hstruct : ∀ j ∈ A, u 0 j = c j ∧ ∀ t : Fin (k + 1), t ≠ 0 → u t j = 0 := by
    intro j hj
    rw [hAdef, Finset.mem_filter] at hj
    have hperm : ∀ z : F, ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t j = c j := hj.2
    set pj : F[X] :=
      (∑ t : Fin (k + 1), Polynomial.monomial (t : ℕ) (u t j)) - Polynomial.C (c j) with hpjdef
    have hpjeval : ∀ z : F, pj.eval z = 0 := by
      intro z
      rw [hpjdef, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_finset_sum]
      have : (∑ t : Fin (k + 1), (Polynomial.monomial (t : ℕ) (u t j)).eval z)
          = ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t j := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Polynomial.eval_monomial]; ring
      rw [this, hperm z]; ring
    have hpjdeg : pj.natDegree ≤ k := by
      rw [hpjdef]
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      simp only [Polynomial.natDegree_C, Nat.max_eq_left (Nat.zero_le _)]
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      exact ⟨Nat.zero_le _, fun t _ =>
        (Polynomial.natDegree_monomial_le _).trans (by exact_mod_cast Nat.lt_succ_iff.mp t.2)⟩
    have hpj0 : pj = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero pj Function.injective_id hpjeval
        (lt_of_le_of_lt hpjdeg hk)
    -- coefficient extraction
    have hcoeff : ∀ t : Fin (k + 1),
        u t j = (Polynomial.C (c j)).coeff (t : ℕ) := by
      intro t
      have h := congrArg (fun p : F[X] => p.coeff (t : ℕ)) hpj0
      simp only [hpjdef, Polynomial.coeff_sub, Polynomial.coeff_zero] at h
      rw [sumMonomial_coeff] at h
      exact sub_eq_zero.mp h
    refine ⟨?_, ?_⟩
    · have := hcoeff 0
      simpa using this
    · intro t ht
      have := hcoeff t
      have hne : (t : ℕ) ≠ 0 := by
        intro hc0; exact ht (Fin.ext hc0)
      simpa [Polynomial.coeff_C, hne] using this
  -- assemble
  refine ⟨A, ?_, fun i => if i = 0 then c else 0, ?_⟩
  · calc (1 - δ) * (Fintype.card ι : ℝ≥0)
        ≤ ((Fintype.card ι - e : ℕ) : ℝ≥0) := hsize
      _ ≤ (A.card : ℝ≥0) := by exact_mod_cast hA
  · intro i
    by_cases hi : i = 0
    · subst hi
      refine ⟨by simpa using hc, ?_⟩
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using (hstruct j hj).1.symm
    · refine ⟨by simpa [hi] using h0, ?_⟩
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi, if_false]
      exact ((hstruct j hj).2 i hi).symm

end ProximityGap
