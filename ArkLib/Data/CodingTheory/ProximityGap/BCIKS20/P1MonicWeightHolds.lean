/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicWeightRefutation

/-!
# BCIKS20 Appendix A.4 (P1) — the weight-1 bound HOLDS on the good instance (#138)

The positive companion to `weight_refuted`.  The (P1) weight invariant of #138 is false-as-stated
because `ClaimA2.Hypotheses` does not bound `deg R`; `weight_refuted` exhibits failure on
`R = Y² − 2 + u·s` (the lift direction carries ground-`X` degree, giving cleared weight `2 > 1`).
This file exhibits the matching success on `R = Y² − 2 + u` (lift direction a constant): the unique
cleared quotient `a = mk(monomial 1 (−1))` has `Λ_𝒪`-weight exactly `1 ≤ 1`.  Together the two pin
the **exact boundary** of the carved predicate: the weight-1 invariant holds iff the lift direction
is free of ground-`X` degree — i.e. the genuine BCIKS20 invariant is the carved predicate plus a
`deg R` bound.  Axiom-clean.
-/

noncomputable section
open scoped Polynomial.Bivariate
open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.WeightWitness

/-- **Good** `R = Y² − 2 + u`: the lift direction is a constant (no ground-`X`), so — unlike the
`weight_refuted` instance `R = Y² − 2 + u·s` — the weight-1 bound HOLDS. -/
abbrev myRG : K[X][X][Y] :=
  Polynomial.monomial 2 (1 : K[X][X]) + Polynomial.monomial 0 ((Polynomial.X : K[X][X]) - 2)

lemma evalX_myRG : Bivariate.evalX (Polynomial.C (0 : K)) myRG = myH := by
  rw [myRG, myH, Bivariate.evalX_eq_map, Polynomial.map_add,
    Polynomial.map_monomial, Polynomial.map_monomial]
  simp only [Polynomial.coe_evalRingHom, map_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.C_0, Polynomial.eval_ofNat, zero_sub]

lemma myHypG : ClaimA2.Hypotheses (0 : K) myRG myH where
  dvd_evalX := by rw [evalX_myRG]
  separable_evalX := by rw [evalX_myRG]; exact myH_separable

/-- The order-1 Hasse coefficient of `RG` specializes to `1` (lift direction is constant). -/
lemma hpG : Bivariate.evalX (Polynomial.C (0 : K)) (hasseDerivX 1 (hasseDerivY 0 myRG))
    = Polynomial.C (1 : K[X]) := by
  rw [hasseDerivY_zero, myRG, hasseDerivX_add, hasseDerivX_monomial, hasseDerivX_monomial]
  simp only [Polynomial.hasseDeriv_one', Polynomial.derivative_one, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_ofNat, sub_zero, Polynomial.monomial_zero_right,
    zero_add]
  rw [Bivariate.evalX_eq_map, Polynomial.map_monomial]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_one, Polynomial.monomial_zero_left]

/-- `β₁ = − mk(1)` (no ground-`X` injected). -/
lemma hβ1G : βHensel myH 0 myRG myHypG 1
    = - Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) (Polynomial.C (1 : K[X])) := by
  rw [βHensel_one_eq myH 0 myRG myHypG]
  simp only [hasseCoeffRepr𝒪]
  rw [hpG]

/-- `ξ = mk(2Y)` (same `∂_Y` as the refutation instance). -/
lemma hξG : ClaimA2.ξ 0 myRG myH myHypG
    = Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) (Polynomial.monomial 1 (2 : K[X])) := by
  have h1 : ClaimA2.ξ 0 myRG myH myHypG
      = Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) (ClaimA2.ξ_pre 0 myRG myH) := rfl
  rw [h1, ξ_pre_eq_of_monic myH 0 myRG myH_leadingCoeff]
  congr 1
  rw [myRG]
  simp only [Polynomial.derivative_add, Polynomial.derivative_monomial, Nat.cast_ofNat,
    Nat.cast_zero, mul_zero, Polynomial.monomial_zero_right, add_zero]
  rw [Bivariate.evalX_eq_map, Polynomial.map_monomial, show (2 - 1 : ℕ) = 1 from rfl]
  congr 1
  simp [Polynomial.coe_evalRingHom]

/-- `weight_Λ (monomial 1 (−1)) = 1` (Y-degree 1, X-degree 0, with `D = d = 2`). -/
lemma hwtG : weight_Λ (Polynomial.monomial 1 (-1 : K[X])) myH 2 = WithBot.some 1 := by
  rw [weight_Λ, Polynomial.support_monomial 1 (by simp : (-1 : K[X]) ≠ 0),
    Finset.sup_singleton, Polynomial.coeff_monomial]
  simp only [if_pos rfl]
  have hnd : (Bivariate.natDegreeY myH) = 2 := myH_natDegree
  rw [hnd]
  norm_num

private lemma h3KXG : (3 : K[X]) = 0 := by
  rw [show (3 : K[X]) = Polynomial.C (3 : K) from (map_ofNat Polynomial.C 3).symm,
    show (3 : K) = 0 from by decide, map_zero]

/-- **The (P1) weight bound HOLDS on the good instance.**  For `RG = Y² − 2 + u` (constant lift
direction), the unique cleared quotient `a = mk(monomial 1 (−1))` of `β₁ = a·ξ` has `Λ_𝒪`-weight
`1 ≤ 1`.  Paired with `weight_refuted` (where `R = Y² − 2 + u·s` gives weight `2 > 1`), this pins the
exact boundary: the weight-1 invariant holds iff the lift direction is free of ground-`X` degree —
i.e. the genuine BCIKS20 invariant is the carved predicate plus a `deg R` bound. -/
theorem weight_holds (hH : 0 < myH.natDegree) :
    ∃ a : 𝒪 myH, βHensel myH 0 myRG myHypG 1 = a * ClaimA2.ξ 0 myRG myH myHypG
        ∧ weight_Λ_over_𝒪 hH a 2 ≤ WithBot.some 1 := by
  refine ⟨Ideal.Quotient.mk (Ideal.span {H_tilde' myH})
      (Polynomial.monomial 1 (-1 : K[X])), ?_, ?_⟩
  · rw [hβ1G, hξG, ← map_mul, Polynomial.monomial_mul_monomial, neg_one_mul,
      show (1 + 1 : ℕ) = 2 from rfl, ← map_neg, Ideal.Quotient.eq,
      H_tilde'_eq_self_of_monic myH myH_leadingCoeff, Ideal.mem_span_singleton]
    refine ⟨Polynomial.C (2 : K[X]), ?_⟩
    rw [myH, add_mul]
    refine Polynomial.ext fun n => ?_
    simp only [Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_C,
      Polynomial.coeff_monomial, Polynomial.coeff_add, Polynomial.coeff_mul_C]
    rcases n with _ | _ | _ | n <;> simp <;>
      first | linear_combination -h3KXG | linear_combination h3KXG
  · have hdeg : (Polynomial.monomial 1 (-1 : K[X])).degree < (H_tilde' myH).degree := by
      rw [H_tilde'_eq_self_of_monic myH myH_leadingCoeff,
        Polynomial.degree_monomial 1 (by simp : (-1 : K[X]) ≠ 0),
        Polynomial.degree_eq_natDegree myH_ne_zero, myH_natDegree]
      exact WithBot.coe_lt_coe.mpr (by norm_num)
    rw [weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hdeg, hwtG]

#print axioms weight_holds

end BCIKS20.HenselNumerator.WeightWitness
