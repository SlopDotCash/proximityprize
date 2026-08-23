/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedList
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSCoveredFraction

/-!
# Sharp interleaved-collapse obstruction at the P1 predecessor

At the P1 rate-quarter predecessor, the witness floor is
`T = 592794966` inside `N = 2^30` coordinates.  The two-row
interleaved collapse therefore queries the code at the doubled floor

```text
A = 2T - N = 111848108.
```

Its numerator is `1 + (N - A) * L`.  This is at most the prize budget
`N` exactly when `L <= 1`; already `L = 2` exceeds the budget.

The required raw uniform `L = 1` premise is false for the rate-quarter
Reed--Solomon code.  Since `A < K = N/4`, take an `A`-set of evaluation
points and the nonzero degree-`A` polynomial vanishing on it.  At the
zero received pair, `(0, 0)` and `(eval(Q), 0)` are two distinct members
of the interleaved list.  Thus the unpruned interleaved-list dictionary
cannot prove the predecessor bound; any successful refinement must use
the bad-event structure rather than a uniform list bound over all stacks.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterInterleavedCollapseNoGo

open ArkLib.CS25
open InterleavedMCACollapse Round17CAPair

/-- P1 block length. -/
abbrev N : Nat := 2 ^ 30

/-- P1 rate-quarter dimension. -/
abbrev K : Nat := 2 ^ 28

/-- Agreement floor at the immediate predecessor. -/
abbrev T : Nat := 592794966

/-- Doubled-radius agreement floor queried by the interleaved collapse. -/
abbrev A : Nat := 2 * T - N

theorem A_eq : A = 111848108 := by
  norm_num [A, T, N]

theorem N_sub_A_eq : N - A = 961893716 := by
  norm_num [A, T, N]

theorem A_lt_K : A < K := by
  norm_num [A, T, N, K]

/-- The raw interleaved-collapse numerator fits the P1 prize budget
exactly for list budgets `L <= 1`. -/
theorem collapseNumerator_le_N_iff (L : Nat) :
    1 + (N - A) * L <= N <-> L <= 1 := by
  norm_num [A, T, N]
  omega

theorem collapseNumerator_one_le :
    1 + (N - A) * 1 <= N := by
  exact (collapseNumerator_le_N_iff 1).2 le_rfl

theorem collapseNumerator_two_not_le :
    ¬ (1 + (N - A) * 2 <= N) := by
  intro h
  have := (collapseNumerator_le_N_iff 2).1 h
  omega

section ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- At the P1 doubled floor the zero received pair has at least two
rate-quarter RS interleaved-list members, for every injective evaluation
domain. -/
theorem two_le_interleavedList_zero (dom : Fin N ↪ F) :
    2 <= (interleavedList (rsCodeFinset dom K)
      (0 : Fin N -> F) (0 : Fin N -> F) A).card := by
  classical
  let emb : Fin A ↪ Fin N :=
    { toFun := fun i =>
        ⟨i, lt_trans i.isLt (by exact A_lt_K.trans (by norm_num [K, N]))⟩
      inj' := by
        intro i j h
        apply Fin.ext
        simpa using congrArg Fin.val h }
  let S : Finset (Fin N) := (Finset.univ : Finset (Fin A)).map emb
  let Q : F[X] := ∏ i : Fin A, (X - C (dom (emb i)))
  let g : Fin N -> F := fun i => Q.eval (dom i)
  have hScard : S.card = A := by
    simp [S]
  have hQmonic : Q.Monic := by
    dsimp [Q]
    exact monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom (emb i)))
  have hQdegree : Q.natDegree = A := by
    dsimp [Q]
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom (emb i)))]
    simp
  have hgC : g ∈ rsCodeFinset dom K := by
    rw [mem_rsCodeFinset]
    refine ⟨Q, Polynomial.mem_degreeLT.mpr ?_, rfl⟩
    rw [Polynomial.degree_eq_natDegree hQmonic.ne_zero, hQdegree]
    exact_mod_cast A_lt_K
  have hzeroC : (0 : Fin N -> F) ∈ rsCodeFinset dom K := by
    rw [mem_rsCodeFinset]
    exact Submodule.zero_mem _
  have hgS : ∀ i ∈ S, g i = 0 := by
    intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hi
    dsimp [g, Q]
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp
  let outside : Fin N := ⟨A, A_lt_K.trans (by norm_num [K, N])⟩
  have hgOutside : g outside ≠ 0 := by
    dsimp [g, Q]
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _hi
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply sub_ne_zero.mpr
    apply dom.injective.ne
    intro h
    have hv := congrArg Fin.val h
    simp [emb, outside] at hv
    exact (Nat.ne_of_lt i.isLt) hv.symm
  have hg_ne : g ≠ (0 : Fin N -> F) := by
    intro h
    exact hgOutside (congrFun h outside)
  let p0 : (Fin N -> F) × (Fin N -> F) := (0, 0)
  let p1 : (Fin N -> F) × (Fin N -> F) := (g, 0)
  have hp0 : p0 ∈ interleavedList (rsCodeFinset dom K)
      (0 : Fin N -> F) (0 : Fin N -> F) A := by
    simp [p0, interleavedList, jointAgreeSet, hzeroC, A, T, N]
  have hp1 : p1 ∈ interleavedList (rsCodeFinset dom K)
      (0 : Fin N -> F) (0 : Fin N -> F) A := by
    rw [interleavedList, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hgC, hzeroC⟩, ?_⟩
    rw [← hScard]
    apply Finset.card_le_card
    intro i hi
    simp only [p1, jointAgreeSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Pi.zero_apply]
    exact ⟨(hgS i hi).symm, trivial⟩
  have hp_ne : p0 ≠ p1 := by
    intro h
    exact hg_ne (by simpa [p0, p1] using (congrArg Prod.fst h).symm)
  have hcard : 1 < (interleavedList (rsCodeFinset dom K)
      (0 : Fin N -> F) (0 : Fin N -> F) A).card :=
    Finset.one_lt_card.mpr ⟨p0, hp0, p1, hp1, hp_ne⟩
  omega

/-- Consequently the raw uniform `L = 1` hypothesis consumed by
`epsMCA_le_of_interleavedList_card_le` is false at the P1 doubled floor. -/
theorem not_uniform_interleavedList_card_le_one (dom : Fin N ↪ F) :
    ¬ (∀ u0 u1 : Fin N -> F,
      (interleavedList (rsCodeFinset dom K) u0 u1 A).card <= 1) := by
  intro h
  have htwo := two_le_interleavedList_zero dom
  have hone := h 0 0
  omega

end ReedSolomon

end ArkLib.ProximityGap.Frontier.P1RateQuarterInterleavedCollapseNoGo

open ArkLib.ProximityGap.Frontier.P1RateQuarterInterleavedCollapseNoGo
#print axioms collapseNumerator_le_N_iff
#print axioms two_le_interleavedList_zero
#print axioms not_uniform_interleavedList_card_le_one
