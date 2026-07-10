/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

/-!
# Support-locator rational fibers

If `H` has degree `s` and a nonzero numerator `r` has degree strictly below
`s`, then every fiber of the rational function `r/H` contains at most `s`
points of an injected evaluation domain.  The statement is written without
division: the fiber at `a` is `r(x)=a*H(x)`.

For a sparse normalized Reed--Solomon direction, `H` is the locator of the
moving support and `r` is its degree-bounded interpolation polynomial.  This
is the scalable algebraic reason that coordinate-line multiplicities are at
most the support size.
-/

set_option autoImplicit false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R400SupportLocatorRationalFiberBound

variable {I F : Type} [Fintype I]
variable [Field F]

/-- A lower-degree nonzero numerator cannot be a scalar multiple of the
degree-`s` denominator. -/
theorem sub_C_mul_ne_zero_of_natDegree_lt
    {r H : F[X]} {s : Nat} (hr : r ≠ 0) (hrdeg : r.natDegree < s)
    (hHdeg : H.natDegree = s) (a : F) :
    r - C a * H ≠ 0 := by
  intro hzero
  have heq : r = C a * H := sub_eq_zero.mp hzero
  by_cases ha : a = 0
  · subst a
    simp only [C_0, zero_mul] at heq
    exact hr heq
  · have hdeg : (C a * H).natDegree = H.natDegree := by
      rw [natDegree_C_mul ha]
    rw [heq, hdeg, hHdeg] at hrdeg
    omega

open Classical in
/-- **Support-locator fiber bound.**  On any injected evaluation domain, the
fiber `r(x)=a*H(x)` has cardinality at most `deg H = s`. -/
theorem rationalFiber_card_le
    (dom : I ↪ F) {r H : F[X]} {s : Nat}
    (hr : r ≠ 0) (hrdeg : r.natDegree < s)
    (hHdeg : H.natDegree = s) (a : F) :
    (Finset.univ.filter fun i =>
      r.eval (dom i) = a * H.eval (dom i)).card ≤ s := by
  let P : F[X] := r - C a * H
  have hP : P ≠ 0 := sub_C_mul_ne_zero_of_natDegree_lt hr hrdeg hHdeg a
  have hdeg : P.natDegree ≤ s := by
    dsimp only [P]
    calc
      (r - C a * H).natDegree ≤ max r.natDegree (C a * H).natDegree :=
        natDegree_sub_le _ _
      _ ≤ s := by
        apply max_le
        · omega
        · exact (natDegree_C_mul_le a H).trans_eq hHdeg
  let S := Finset.univ.filter fun i =>
    r.eval (dom i) = a * H.eval (dom i)
  let e : I ↪ F := dom
  have hroots : S.map e ⊆ P.roots.toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots hP]
    have hi' : r.eval (dom i) = a * H.eval (dom i) := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact (show P.eval (dom i) = 0 by
      dsimp only [P]
      rw [eval_sub, eval_mul, eval_C, hi', sub_self])
  calc
    S.card = (S.map e).card := by rw [Finset.card_map]
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ s := hdeg

#print axioms sub_C_mul_ne_zero_of_natDegree_lt
#print axioms rationalFiber_card_le

end ArkLib.ProximityGap.Frontier.R400SupportLocatorRationalFiberBound
