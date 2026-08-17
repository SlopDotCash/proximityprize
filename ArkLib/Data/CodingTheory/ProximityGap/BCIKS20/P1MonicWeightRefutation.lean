/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality

/-!
# BCIKS20 Appendix A.4 (P1) — the weight bound is FALSE under `ClaimA2.Hypotheses` (#138)

A concrete, axiom-clean refutation of the (P1) weight-1 invariant for monic `H`, on a **valid
separable** `ClaimA2.Hypotheses` instance.  Integrality of `αGenuine` holds
  (`alphaGenuine_regular_of_monic`),
but the **weight** conjunct of `AlphaGenuineRegularWeightLe` / `SuccDivWeightLe_of_monic` fails:
`ClaimA2.Hypotheses` (`dvd_evalX` + `separable_evalX`) does **not** bound `deg R`, so the lift
direction injects `X`-degree that division by `ξ` (`Y`-degree 1) shifts onto a `Y`-power, breaking
`Λ_𝒪 ≤ Λ(Y) = 1`.

* `K = ZMod 3`, `H = Y² − 2` (monic, irreducible — no `c` with `c²=2`; separable — `disc 8` a unit).
* `R = Y² − 2 + u·s`, `x₀ = 0`: `evalX(C 0) R = H`, so `dvd`+`separable` hold (valid).
* `β₁ = −mk(C s)` (weight 1), `ξ = mk(2Y)` a unit, so the unique quotient `β₁ = a·ξ` is
  `a = mk(monomial 1 (−X))` of **weight 2 > 1**.

`weight_refuted` is the negation of `SuccDivWeightLe_of_monic`'s `t = 0` case (`ξ^(2·0+1) = ξ`).
Together with the proven integrality half, this shows the (P1) predicate is **not a theorem** under
the in-tree hypotheses — the third carved residual found false-as-stated (cf. #139, #140); the fix
  is
to bound `deg R` relative to `D` (BCIKS20's `R` is degree-bounded), as the genuine theorem requires.
-/

noncomputable section
open scoped Polynomial.Bivariate
open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.WeightWitness

instance primeFact_P1MonicWeightRefutation_1 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
abbrev K := ZMod 3

/-- Monic separable irreducible `H = Y² − 2` over `(ZMod 3)[X]`. -/
abbrev myH : K[X][Y] := Polynomial.monomial 2 (1 : K[X]) + Polynomial.monomial 0 (-2 : K[X])

/-- `R = Y² − 2 + u·s` (`u` = lift var, `s` = ground var): the high lift-direction degree breaks the
weight while keeping `ClaimA2.Hypotheses` (degree of `R` is unconstrained by `dvd`+`separable`). -/
abbrev myR : K[X][X][Y] :=
  Polynomial.monomial 2 (1 : K[X][X])
    + Polynomial.monomial 0 (Polynomial.X * Polynomial.C (Polynomial.X : K[X]) - 2)

lemma hasseDerivX_monomial (i1 k : ℕ) (a : K[X][X]) :
    hasseDerivX i1 (Polynomial.monomial k a)
      = Polynomial.monomial k (Polynomial.hasseDeriv i1 a) := by
  unfold hasseDerivX
  exact Polynomial.sum_monomial_index a _ (by simp)

lemma myH_natDegree : myH.natDegree = 2 := by
  unfold myH; compute_degree!

lemma myH_monic : myH.Monic := by
  unfold myH; monicity!

lemma myH_leadingCoeff : myH.leadingCoeff = 1 := myH_monic

lemma myH_ne_zero : myH ≠ 0 := myH_monic.ne_zero

lemma myH_roots : myH.roots = 0 := by
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro a ha
  rw [Polynomial.mem_roots myH_ne_zero, Polynomial.IsRoot.def, myH] at ha
  simp only [Polynomial.eval_add, Polynomial.eval_monomial, pow_zero, mul_one] at ha
  have hsq : a ^ 2 = 2 := by linear_combination ha
  have he : (a.eval 0) ^ 2 = 2 := by rw [← Polynomial.eval_pow, hsq]; simp
  exact (by decide : ∀ d : K, d ^ 2 ≠ 2) (a.eval 0) he

lemma myH_irreducible : Irreducible myH :=
  (myH_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [myH_natDegree]) (by rw [myH_natDegree]; norm_num)).mpr myH_roots

instance instFactIrr : Fact (Irreducible myH) := ⟨myH_irreducible⟩
instance instFactDeg : Fact (0 < myH.natDegree) := ⟨by rw [myH_natDegree]; norm_num⟩

lemma myR_natDegree : myR.natDegree = 2 := by
  unfold myR; compute_degree!

lemma evalX_myR : Bivariate.evalX (Polynomial.C (0 : K)) myR = myH := by
  rw [myR, myH, Bivariate.evalX_eq_map, Polynomial.map_add,
    Polynomial.map_monomial, Polynomial.map_monomial]
  simp only [Polynomial.coe_evalRingHom, map_sub, map_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.C_0, zero_mul, Polynomial.eval_one,
    Polynomial.monomial_zero_right, zero_sub, ← Polynomial.monomial_neg, Polynomial.eval_ofNat]

lemma myH_separable : myH.Separable := by
  rw [Polynomial.separable_def, myH]
  refine ⟨1, Polynomial.X, ?_⟩
  have h3 : (3 : K[X]) = 0 := by
    rw [show (3 : K[X]) = Polynomial.C (3 : K) from (map_ofNat Polynomial.C 3).symm,
      show (3 : K) = 0 from by decide, map_zero]
  have hm2 : (-2 : K[X]) = 1 := by linear_combination -h3
  simp only [Polynomial.derivative_add, Polynomial.derivative_monomial,
    one_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, Polynomial.monomial_zero_right, add_zero]
  rw [Polynomial.X_mul_monomial, show (2 - 1 + 1 : ℕ) = 2 from rfl, add_right_comm,
    ← Polynomial.monomial_add, show (1 : K[X]) + 2 = 3 from by ring, h3,
    Polynomial.monomial_zero_right, zero_add, hm2, Polynomial.monomial_zero_left, map_one]

lemma myHyp : ClaimA2.Hypotheses (0 : K) myR myH where
  dvd_evalX := by rw [evalX_myR]
  separable_evalX := by rw [evalX_myR]; exact myH_separable

/-- The order-1 Hasse coefficient of `R` specializes to `C s` (the ground variable). -/
lemma hp : Bivariate.evalX (Polynomial.C (0 : K)) (hasseDerivX 1 (hasseDerivY 0 myR))
    = Polynomial.C (Polynomial.X : K[X]) := by
  rw [hasseDerivY_zero, myR, hasseDerivX_add, hasseDerivX_monomial, hasseDerivX_monomial]
  simp only [Polynomial.hasseDeriv_one', Polynomial.derivative_one, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.derivative_C, mul_zero,
    add_zero, one_mul, Polynomial.derivative_ofNat, sub_zero, Polynomial.monomial_zero_right,
    zero_add]
  rw [Bivariate.evalX_eq_map, Polynomial.map_monomial]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.monomial_zero_left]

/-- `β₁ = − mk(C s)` — minus the (degree-1) ground variable, lifted into `𝒪`. -/
lemma hβ1 : βHensel myH 0 myR myHyp 1
    = - Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) (Polynomial.C (Polynomial.X : K[X])) := by
  rw [βHensel_one_eq myH 0 myR myHyp]
  simp only [hasseCoeffRepr𝒪]
  rw [hp]

/-- `ξ = mk(2Y)`. -/
lemma hξ : ClaimA2.ξ 0 myR myH myHyp
    = Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) (Polynomial.monomial 1 (2 : K[X])) := by
  have h1 : ClaimA2.ξ 0 myR myH myHyp
      = Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) (ClaimA2.ξ_pre 0 myR myH) := rfl
  rw [h1, ξ_pre_eq_of_monic myH 0 myR myH_leadingCoeff]
  congr 1
  rw [myR]
  simp only [Polynomial.derivative_add, Polynomial.derivative_monomial, Nat.cast_ofNat,
    Nat.cast_zero, mul_zero, Polynomial.monomial_zero_right, add_zero]
  rw [Bivariate.evalX_eq_map, Polynomial.map_monomial, show (2 - 1 : ℕ) = 1 from rfl]
  congr 1
  simp [Polynomial.coe_evalRingHom]

private lemma h3KX : (3 : K[X]) = 0 := by
  rw [show (3 : K[X]) = Polynomial.C (3 : K) from (map_ofNat Polynomial.C 3).symm,
    show (3 : K) = 0 from by decide, map_zero]

/-- `ξ` is a unit, with inverse `mk(Y)` (since `2Y·Y = 2Y² = 4 = 1` in `ZMod 3`). -/
lemma hξinv : ClaimA2.ξ 0 myR myH myHyp
    * Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) Polynomial.X = 1 := by
  rw [hξ, ← map_mul, Polynomial.monomial_mul_X]
  rw [show (1 : 𝒪 myH) = Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) 1 from (map_one _).symm]
  rw [Ideal.Quotient.eq, H_tilde'_eq_self_of_monic myH myH_leadingCoeff,
    Ideal.mem_span_singleton]
  refine ⟨Polynomial.C 2, ?_⟩
  rw [myH, add_mul, Polynomial.monomial_mul_C, Polynomial.monomial_mul_C,
    show (1 + 1 : ℕ) = 2 from rfl, show (1 : K[X]) * 2 = 2 from by ring,
    show (1 : K[X][Y]) = Polynomial.monomial 0 (1 : K[X]) from by
      rw [Polynomial.monomial_zero_left, map_one],
    sub_eq_add_neg, ← Polynomial.monomial_neg, add_right_inj]
  congr 1
  linear_combination h3KX

/-- `weight_Λ (monomial 1 (−X)) = 2 > 1`. -/
lemma hwt : weight_Λ (Polynomial.monomial 1 (-(Polynomial.X : K[X]))) myH 2 = WithBot.some 2 := by
  rw [weight_Λ, Polynomial.support_monomial 1 (by simp : (-(Polynomial.X : K[X])) ≠ 0),
    Finset.sup_singleton, Polynomial.coeff_monomial]
  simp only [if_pos rfl]
  have hnd : (Bivariate.natDegreeY myH) = 2 := myH_natDegree
  rw [hnd]
  norm_num

/-- **The (P1) weight bound is FALSE on a valid separable instance.**  At order 1 the only
`𝒪`-preimage `a` of `αGenuine 1` (equivalently the unique quotient `β₁ = a·ξ`, `ξ` a unit) is
`mk(monomial 1 (−X))`, whose `Λ_𝒪`-weight is `2 > 1`.  So `SuccDivWeightLe_of_monic` / the (P1)
weight invariant `AlphaGenuineRegularWeightLe` is **not a theorem** under `ClaimA2.Hypotheses` — the
two-field hypothesis (`dvd`+`separable`) does not bound `deg R`, so the lift direction injects
`X`-degree that `ξ`-division shifts onto a `Y`-power, breaking `Λ ≤ Λ(Y) = 1`. -/
theorem weight_refuted (hH : 0 < myH.natDegree) :
    ¬ ∃ a : 𝒪 myH, βHensel myH 0 myR myHyp 1 = a * ClaimA2.ξ 0 myR myH myHyp
        ∧ weight_Λ_over_𝒪 hH a 2 ≤ WithBot.some 1 := by
  rintro ⟨a, ha_eq, ha_wt⟩
  have ha : a = Ideal.Quotient.mk (Ideal.span {H_tilde' myH})
      (Polynomial.monomial 1 (-(Polynomial.X : K[X]))) := by
    have hstep : a = βHensel myH 0 myR myHyp 1
        * Ideal.Quotient.mk (Ideal.span {H_tilde' myH}) Polynomial.X := by
      conv_lhs => rw [← mul_one a, ← hξinv, ← mul_assoc, ← ha_eq]
    rw [hstep, hβ1, neg_mul, ← map_mul, ← map_neg]
    congr 1
    rw [show Polynomial.C (Polynomial.X : K[X]) = Polynomial.monomial 0 (Polynomial.X : K[X]) from
        (Polynomial.monomial_zero_left _).symm, Polynomial.monomial_mul_X,
      ← Polynomial.monomial_neg]
  have hdeg : (Polynomial.monomial 1 (-(Polynomial.X : K[X]))).degree < (H_tilde' myH).degree := by
    rw [H_tilde'_eq_self_of_monic myH myH_leadingCoeff,
      Polynomial.degree_monomial 1 (by simp : (-(Polynomial.X : K[X])) ≠ 0),
      Polynomial.degree_eq_natDegree myH_ne_zero, myH_natDegree]
    decide
  rw [ha, weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hdeg, hwt] at ha_wt
  exact absurd ha_wt (by decide)

#print axioms weight_refuted

end BCIKS20.HenselNumerator.WeightWitness
