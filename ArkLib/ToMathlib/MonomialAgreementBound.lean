/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots

/-!
# Monomial agreement bound — the Lift-Lemma far-ness count (issue #232)

A monomial word `x ↦ x^a` agrees with any polynomial of degree `< k ≤ a` on at most `a`
points: `X^a − c` is nonzero of degree `≤ a`, so it has at most `a` roots. This is the
one-line far-ness ingredient of the averaged lower half's Lift Lemma (research note
`06-AVERAGED-PA.md`; DISPROOF_LOG O11⁗⁺): the pair `(x^{rc}, x^{(r−1)c})` with
`(r−1)c = k` is automatically MCA-far at the construction's radius.
-/

open Polynomial

namespace ArkLib.SmoothDomain

variable {F : Type*} [Field F]

open Classical in
/-- **Far-ness degree count.** A monomial word `x ↦ x^a` agrees with any polynomial of degree
`< k ≤ a` on at most `a` points of any evaluation set. -/
theorem agreement_card_le_of_natDegree_lt (H : Finset F) (a k : ℕ)
    (c : F[X]) (hc : c.natDegree < k) (hk : k ≤ a) :
    (H.filter (fun x => x ^ a = c.eval x)).card ≤ a := by
  classical
  set P : F[X] := X ^ a - c with hPdef
  have hca : c.coeff a = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hc hk)
  have hPne : P ≠ 0 := by
    intro h
    have : P.coeff a = 0 := by rw [h]; simp
    rw [hPdef, coeff_sub, coeff_X_pow, if_pos rfl, hca, sub_zero] at this
    exact one_ne_zero this
  have hPdeg : P.natDegree ≤ a := by
    apply le_trans (natDegree_sub_le _ _)
    simp only [natDegree_X_pow]
    exact max_le le_rfl (le_trans (le_of_lt hc) hk)
  have hsub : H.filter (fun x => x ^ a = c.eval x) ⊆ P.roots.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Multiset.mem_toFinset, mem_roots hPne]
    simp only [IsRoot, hPdef, eval_sub, eval_pow, eval_X]
    rw [hx.2]; ring
  calc (H.filter (fun x => x ^ a = c.eval x)).card
      ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ a := hPdeg


end ArkLib.SmoothDomain

#print axioms ArkLib.SmoothDomain.agreement_card_le_of_natDegree_lt
