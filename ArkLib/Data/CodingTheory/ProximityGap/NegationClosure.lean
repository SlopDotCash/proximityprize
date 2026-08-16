/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Expand

/-!
# Negation-closure from even generating polynomials (proximity-prize coset-saturation seed)

The value-level core of dyadic `μ₂`-coset-saturation: an even monic generating polynomial forces the
root multiset to be `±`-pair-closed. With the `m=2` gap (`e₁=e₃=0`, size 4) the configuration polynomial
`X⁴+e₂X²+e₄` is even, so the agreement set is a union of `μ₂`-cosets — the rigorous, char-`p`-free
minimal case of the proximity-prize optimality (`#bad ≤ |Σ_r|` at `r=2`, any field). Complements
`FactorizationRigidity.lean` (the `m`-sparse ⟺ `μ_m`-coset-union statement) at the multiset-value level.
-/

namespace ArkLib.ProximityGap.NegClosure
open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

private lemma factor_comp_neg (a : R) :
    (X - C a).comp (-X) = C (-1) * (X - C (-a)) := by
  simp [sub_comp, X_comp, C_comp]; ring

/-- **Negation-closure brick.** If the monic generating polynomial `∏_{a∈S}(X-a)` of a finite root
multiset over an integral domain is even (`P.comp(-X) = P`), then `S` is closed under negation. -/
theorem neg_closed_of_even {S : Multiset R}
    (heven : ((S.map fun a => X - C a).prod).comp (-X) = (S.map fun a => X - C a).prod) :
    S.map (fun a => -a) = S := by
  have hcomp : ((S.map fun a => X - C a).prod).comp (-X)
      = C ((-1 : R) ^ S.card) * ((S.map fun a => -a).map fun a => X - C a).prod := by
    rw [multiset_prod_comp, Multiset.map_map]
    have e1 : (S.map ((fun p => p.comp (-X)) ∘ fun a => X - C a))
        = S.map fun a => C (-1) * (X - C (-a)) :=
      Multiset.map_congr rfl (fun a _ => factor_comp_neg a)
    rw [e1, Multiset.prod_map_mul, Multiset.map_map]
    congr 1
    simp [Multiset.map_const', Multiset.prod_replicate, C_pow]
  rw [heven] at hcomp
  have hc : ((-1 : R) ^ S.card) ≠ 0 := pow_ne_zero _ (by simp)
  have h2 : ((S.map fun a => X - C a).prod).roots
          = ((S.map fun a => -a).map fun a => X - C a).prod.roots := by
    rw [hcomp, roots_C_mul _ hc]
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h2
  exact h2.symm

/-- An `X²`-polynomial (`expand R 2 g`, supported on even degrees) is invariant under `X ↦ -X`. -/
private lemma expand_two_comp_neg (g : R[X]) : (expand R 2 g).comp (-X) = expand R 2 g := by
  rw [expand_eq_comp_X_pow, comp_assoc]
  congr 1
  simp [neg_pow, pow_two]

/-- **Corollary (m=2 coset-saturation seed).** If the generating polynomial of the root multiset `S`
is a polynomial in `X²` (`= expand R 2 g`, i.e. supported only on even degrees — the `2`-sparse /
`e_odd = 0` condition), then `S` is closed under negation, hence a union of `±`-pairs (`μ₂`-cosets). -/
theorem neg_closed_of_expand_two {S : Multiset R} {g : R[X]}
    (hg : (S.map fun a => X - C a).prod = expand R 2 g) :
    S.map (fun a => -a) = S := by
  apply neg_closed_of_even
  rw [hg]; exact expand_two_comp_neg g

end ArkLib.ProximityGap.NegClosure
