/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-!
# The twisted-kernel lemma for smooth (2-adic) domains (issue #232)

The σ-twisted kernel systems arising from the even/odd (FRI-fold) descent on 2-power smooth
domains are **unconditionally trivial**: if `e, f` have degree `< κ` and
`e(d²) + d·f(d²) = 0` at `2κ` distinct points `d`, then `e = f = 0` — because
`P(d) := e(d²) + d·f(d²)` is a polynomial of degree `≤ 2κ−1` with `2κ` roots, and the
even/odd parts of `P = 0` recover `e` and `f` (composition with `−X` plus `char ≠ 2`).

This is the mechanism-level fact "what smoothness supplies": the parametrization `z = d²`
gives rigidity that random evaluation domains only get generically. Consequences (see the
DISPROOF_LOG O14): in the descent's overdetermined pattern systems, solutions are unique per
pattern, so beyond-Johnson list bounds reduce to inhomogeneous consistency counting.
-/

open Polynomial

namespace ArkLib.SmoothDomain

variable {F : Type*} [Field F]

/-- **Twisted-kernel triviality.** If `deg e, deg f < κ` and `e(d²) + d·f(d²) = 0` on a set of
`2κ` distinct points, then `e = f = 0`. Unconditional (only `char F ≠ 2` via `(2 : F) ≠ 0`). -/
theorem twisted_kernel_trivial (h2 : (2 : F) ≠ 0) {κ : ℕ}
    {e f : F[X]} (he : e.natDegree < κ) (hf : f.natDegree < κ)
    (D : Finset F) (hD : 2 * κ ≤ D.card)
    (hroot : ∀ d ∈ D, e.eval (d ^ 2) + d * f.eval (d ^ 2) = 0) :
    e = 0 ∧ f = 0 := by
  classical
  set P : F[X] := e.comp (X ^ 2) + X * f.comp (X ^ 2) with hPdef
  have hdegX2 : (X ^ 2 : F[X]).natDegree = 2 := natDegree_X_pow 2
  have hPdeg : P.natDegree < 2 * κ := by
    have h1 : (e.comp (X ^ 2)).natDegree < 2 * κ := by
      rw [natDegree_comp, hdegX2]; omega
    have h2' : (X * f.comp (X ^ 2)).natDegree < 2 * κ := by
      calc (X * f.comp (X ^ 2)).natDegree
          ≤ X.natDegree + (f.comp (X ^ 2)).natDegree := natDegree_mul_le
        _ = 1 + f.natDegree * 2 := by rw [natDegree_X, natDegree_comp, hdegX2]
        _ < 2 * κ := by omega
    exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt h1 h2')
  have hP0 : P = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P D
    · intro d hd
      simp only [hPdef, eval_add, eval_mul, eval_comp, eval_pow, eval_X]
      exact hroot d hd
    · exact lt_of_lt_of_le hPdeg hD
  have hP0' : e.comp (X ^ 2) + X * f.comp (X ^ 2) = 0 := by rw [← hPdef]; exact hP0
  have hPneg : e.comp (X ^ 2) - X * f.comp (X ^ 2) = 0 := by
    have h := congrArg (fun p : F[X] => p.comp (-X)) hP0
    simp only [hPdef, add_comp, mul_comp, comp_assoc, X_comp, pow_comp, zero_comp] at h
    rw [neg_pow, show ((-1 : F[X]) ^ 2) = 1 by ring, one_mul] at h
    linear_combination h
  have h2X : (2 : F[X]) ≠ 0 := by
    have hC : (2 : F[X]) = C (2 : F) := (map_ofNat (C : F →+* F[X]) 2).symm
    rw [hC, Ne, C_eq_zero]; exact h2
  have heC : e.comp (X ^ 2) = 0 := by
    have hsum : (2 : F[X]) * e.comp (X ^ 2) = 0 := by linear_combination hP0' + hPneg
    exact (mul_eq_zero.mp hsum).resolve_left h2X
  have hfC : f.comp (X ^ 2) = 0 := by
    have hx : (X : F[X]) * f.comp (X ^ 2) = 0 := by linear_combination hP0' - heC
    exact (mul_eq_zero.mp hx).resolve_left X_ne_zero
  have hcomp : ∀ g : F[X], g.comp (X ^ 2) = 0 → g = 0 := by
    intro g hg
    by_contra hne
    have hlc := leadingCoeff_comp (p := g) (q := X ^ 2) (by rw [hdegX2]; omega)
    rw [hg] at hlc
    simp only [leadingCoeff_zero, leadingCoeff_X_pow, one_pow, mul_one] at hlc
    exact hne (leadingCoeff_eq_zero.mp hlc.symm)
  exact ⟨hcomp e heC, hcomp f hfC⟩


end ArkLib.SmoothDomain

#print axioms ArkLib.SmoothDomain.twisted_kernel_trivial
