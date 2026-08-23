/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly

/-!
# Polynomial-level additivity of the subspace polynomial

The repo's `BKR06.subspacePoly_eval_add` proves the *evaluation* map `x ↦ P_L(x)` is additive when
`L` is a finite additive subgroup.  This file exposes the corresponding **polynomial identity**

`(subspacePoly L).comp (X + C y) = subspacePoly L + C ((subspacePoly L).eval y)`,

i.e. `P_L(X + y) = P_L(X) + P_L(y)` as polynomials in `X`.  This is the linearized-polynomial form
that the subspace-polynomial recursion `s_{V'⊕𝔽_q·u} = ∏_{c∈F}(s_{V'} - C(c·s_{V'}(u)))` consumes
(via the translation `s_{V'}(X - c·u) = s_{V'}(X) - s_{V'}(c·u)`).

Proof: the polynomial `r = P_L(X+y) - P_L(X) - C(P_L(y))` has `natDegree < |L|` (the two monic
degree-`|L|` terms cancel) and vanishes on all of `L` (by eval-additivity and `P_L|_L = 0`), hence
`r = 0`.
-/

open Polynomial BigOperators

namespace BKR06

variable {K : Type*} [Field K]

/-- **Polynomial additivity of the subspace polynomial.** For a finite additive subgroup `L ⊆ K`,
`(subspacePoly L).comp (X + C y) = subspacePoly L + C ((subspacePoly L).eval y)` as polynomials. -/
theorem subspacePoly_comp_X_add_C_eq
    (L : Finset K) (h0 : (0 : K) ∈ L)
    (hsub : ∀ x ∈ L, ∀ y ∈ L, x - y ∈ L)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L) (y : K) :
    (subspacePoly L).comp (X + C y) = subspacePoly L + C ((subspacePoly L).eval y) := by
  classical
  have hcard_pos : 0 < L.card := Finset.card_pos.2 ⟨0, h0⟩
  have hcard_ne : L.card ≠ 0 := hcard_pos.ne'
  have hmon1 : IsMonicOfDegree ((subspacePoly L).comp (X + C y)) L.card := by
    refine ⟨?_, (subspacePoly_monic L).comp_X_add_C y⟩
    rw [← taylor_apply, natDegree_taylor, subspacePoly_natDegree]
  have hmon2 : IsMonicOfDegree (subspacePoly L) L.card := subspacePoly_isMonicOfDegree L
  have hq₁ : ((subspacePoly L).comp (X + C y) - subspacePoly L).natDegree < L.card :=
    hmon1.natDegree_sub_lt hcard_ne hmon2
  set r : K[X] :=
    (subspacePoly L).comp (X + C y) - subspacePoly L - C ((subspacePoly L).eval y) with hr_def
  have hr_deg : r.natDegree < L.card := by
    have hC : (C ((subspacePoly L).eval y)).natDegree < L.card := by
      rw [natDegree_C]; exact hcard_pos
    calc r.natDegree
        ≤ max ((subspacePoly L).comp (X + C y) - subspacePoly L).natDegree
            (C ((subspacePoly L).eval y)).natDegree := natDegree_sub_le _ _
      _ < L.card := max_lt hq₁ hC
  have hr_vanish : ∀ ℓ ∈ L, r.eval ℓ = 0 := by
    intro ℓ hℓ
    have hev_comp : ((subspacePoly L).comp (X + C y)).eval ℓ
        = (subspacePoly L).eval (ℓ + y) := by rw [eval_comp]; simp
    have hPℓ : (subspacePoly L).eval ℓ = 0 := (subspacePoly_isRoot_iff L ℓ).2 hℓ
    have hadd_ev : (subspacePoly L).eval (ℓ + y)
        = (subspacePoly L).eval ℓ + (subspacePoly L).eval y :=
      subspacePoly_eval_add L h0 hsub hadd ℓ y
    rw [hr_def]
    simp only [eval_sub, eval_C, hev_comp, hadd_ev, hPℓ]
    ring
  have hr_zero : r = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero' r L hr_vanish hr_deg
  rw [hr_def, sub_sub, sub_eq_zero] at hr_zero
  exact hr_zero

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_comp_X_add_C_eq
