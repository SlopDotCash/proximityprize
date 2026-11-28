/-
Copyright (c) 2026 Cheelax. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Cheelax
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicWeightRefutation

/-!
# BCIKS20 Appendix A.4 — both `(A.1)` per-term weight residuals are FALSE as stated

`βHenselSuccTermWeightResidual` (the loose per-term wall that the O154 audit names as the last
residual of the Johnson programme) and its narrowed form
`βHenselSuccTermStructuredWeightResidual` bound the weight of one `(A.1)` recursion term by
`(2(k+1)+1)·d_R·D`.  The bound depends only on `d_R = natDegreeY R` and `D`, but
`ClaimA2.Hypotheses` (`dvd_evalX` + `separable_evalX`) does not bound the ground-`X` degree of `R`.
The same gap broke the (P1) weight invariant in `P1MonicWeightRefutation.lean`.  Here it breaks
both per-term residuals already at the first step, where neither the loose nor the structured
induction hypothesis is used at all.

* `K = ZMod 3`, `H = Y² − 2` (the monic, irreducible, separable `myH` of
  `P1MonicWeightRefutation`), `x₀ = 0`, and `R = Y² − 2 + u·s^N` (`u` = lift variable,
  `s` = ground variable).  `evalX(C 0) R = H`, so `ClaimA2.Hypotheses` holds for every `N`.
* At `k = 0`, `i1 = 1` and the empty partition of `0`, the `W`- and `ξ`-exponents vanish, the
  prefactor is `1`, and the term is `mk(C (s^N))`, of `Λ`-weight exactly `N`.
* The target is `(2·1+1)·2·D = 6D`, so any `N > 6D` violates it.  The loose induction hypothesis
  at `l = 0` is `Λ(β₀) = D − 1 ≤ 2D`, true for every `D ≥ 2`; the structured invariant at `l = 0`
  is `Λ(β₀) ≤ 1`, true at the tight anchor `D = 2`.

Hence `βHenselSuccTermWeightResidual` fails at every `D ≥ 2`, and
`βHenselSuccTermStructuredWeightResidual` fails at `D = 2`.  The genuine BCIKS20 statement carries
a degree bound on `R` relative to `D`; any repaired residual must add it.  Axiom-clean.
-/

noncomputable section
open scoped Polynomial.Bivariate
open Polynomial Polynomial.Bivariate BCIKS20AppendixA

namespace BCIKS20.HenselNumerator.SuccTermWitness

open BCIKS20.HenselNumerator.WeightWitness

/-- `R = Y² − 2 + u·s^N`: the lift direction carries ground-`X` degree `N`, unconstrained by
`ClaimA2.Hypotheses`. -/
abbrev myRN (N : ℕ) : K[X][X][Y] :=
  Polynomial.monomial 2 (1 : K[X][X])
    + Polynomial.monomial 0 (Polynomial.X * Polynomial.C ((Polynomial.X : K[X]) ^ N) - 2)

lemma myRN_natDegreeY (N : ℕ) : Bivariate.natDegreeY (myRN N) = 2 := by
  unfold Bivariate.natDegreeY myRN; compute_degree!

lemma evalX_myRN (N : ℕ) : Bivariate.evalX (Polynomial.C (0 : K)) (myRN N) = myH := by
  rw [myRN, myH, Bivariate.evalX_eq_map, Polynomial.map_add,
    Polynomial.map_monomial, Polynomial.map_monomial]
  simp only [Polynomial.coe_evalRingHom, map_sub, map_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.C_0, zero_mul, Polynomial.eval_one,
    zero_sub, Polynomial.eval_ofNat]

lemma myHypN (N : ℕ) : ClaimA2.Hypotheses (0 : K) (myRN N) myH where
  dvd_evalX := by rw [evalX_myRN]
  separable_evalX := by rw [evalX_myRN]; exact myH_separable

/-- The order-1 lift-direction Hasse coefficient of `R` specializes to `C (s^N)`. -/
lemma hpN (N : ℕ) :
    Bivariate.evalX (Polynomial.C (0 : K)) (hasseDerivX 1 (hasseDerivY 0 (myRN N)))
      = Polynomial.C ((Polynomial.X : K[X]) ^ N) := by
  rw [hasseDerivY_zero, myRN, hasseDerivX_add, hasseDerivX_monomial, hasseDerivX_monomial]
  simp only [Polynomial.hasseDeriv_one', Polynomial.derivative_one, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.derivative_C, mul_zero,
    add_zero, one_mul, Polynomial.derivative_ofNat, sub_zero, Polynomial.monomial_zero_right,
    zero_add]
  rw [Bivariate.evalX_eq_map, Polynomial.map_monomial]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.monomial_zero_left]

lemma myH_totalDegree_le : Bivariate.totalDegree myH ≤ 2 := by
  unfold Bivariate.totalDegree
  refine Finset.sup_le fun m hm => ?_
  have hm2 : m ≤ 2 := myH_natDegree ▸ Polynomial.le_natDegree_of_mem_supp m hm
  interval_cases m <;> simp [myH, Polynomial.coeff_monomial]

lemma myH_tilde_degree : (H_tilde' myH).degree = 2 := by
  rw [H_tilde'_eq_self_of_monic myH myH_leadingCoeff,
    Polynomial.degree_eq_natDegree myH_ne_zero, myH_natDegree]
  rfl

/-- `Λ(β₀) = Λ(mk Y) = D − 1`. -/
lemma weight_β₀ (N : ℕ) (hH : 0 < myH.natDegree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel myH 0 (myRN N) (myHypN N) 0) D
      = WithBot.some (D + 1 - 2) := by
  have hdeg : (Polynomial.X : K[X][Y]).degree < (H_tilde' myH).degree := by
    rw [myH_tilde_degree, Polynomial.degree_X]; decide
  rw [βHensel_zero, weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hdeg, weight_Λ,
    ← Polynomial.monomial_one_one_eq_X, Polynomial.support_monomial 1 one_ne_zero,
    Finset.sup_singleton, Polynomial.coeff_monomial, ite_eq_left rfl]
  have hnd : Bivariate.natDegreeY myH = 2 := myH_natDegree
  rw [hnd]
  simp

/-- The `k = 0`, `i1 = 1`, empty-partition `(A.1)` term is `mk(C (s^N))`, of weight `N`. -/
lemma weight_term (N : ℕ) (hH : 0 < myH.natDegree) (D : ℕ)
    (lam : Nat.Partition (0 + 1 - 1)) :
    weight_Λ_over_𝒪 hH
        ((W𝒪 myH) ^ (1 + deltaSave 1 - 1)
          * (ClaimA2.ξ 0 (myRN N) myH (myHypN N)) ^ (2 * 1 + sigmaLambda lam - 2)
          * B_coeff myH 0 (myRN N) 1 lam
          * partitionProd lam
              (fun l => if _h : l < 0 + 1 then βHensel myH 0 (myRN N) (myHypN N) l else 0)) D
      = WithBot.some N := by
  have hsig : sigmaLambda lam = 0 := by simp [sigmaLambda]
  have hpre : prefactor (myRN N).natDegree 1 lam = 1 := by simp [prefactor]
  have hprod : partitionProd lam
      (fun l => if _h : l < 0 + 1 then βHensel myH 0 (myRN N) (myHypN N) l else 0) = 1 :=
    partitionProd_zero lam _
  have hdeg : (Polynomial.C ((Polynomial.X : K[X]) ^ N)).degree < (H_tilde' myH).degree := by
    rw [myH_tilde_degree]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  rw [hsig, hprod, B_coeff, hpre, one_smul, hasseCoeffRepr𝒪, hsig, hpN]
  simp only [deltaSave, ite_eq_right one_ne_zero, add_zero, Nat.sub_self, pow_zero, one_mul,
    mul_one]
  -- `hprod` leaves `Ideal.Quotient.one`, which `rw [mul_one]` does not match syntactically.
  refine (congrArg (fun x => weight_Λ_over_𝒪 hH x D) (mul_one _)).trans ?_
  rw [weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hdeg, weight_Λ,
    ← Polynomial.monomial_zero_left,
    Polynomial.support_monomial 0 (pow_ne_zero N Polynomial.X_ne_zero),
    Finset.sup_singleton, Polynomial.coeff_monomial, ite_eq_left rfl]
  simp

/-- `R = myRN N` is in the `2 ≤ d_R` regime of both residuals. -/
lemma myRN_two_le (N : ℕ) : 2 ≤ Bivariate.natDegreeY (myRN N) := (myRN_natDegreeY N).ge

/-- The loose induction hypothesis at `k = 0`: `Λ(β₀) = D − 1 ≤ 2D`. -/
lemma loose_ih_zero (N D : ℕ) (hH : 0 < myH.natDegree) :
    ∀ l, l < 0 + 1 →
      weight_Λ_over_𝒪 hH (βHensel myH 0 (myRN N) (myHypN N) l) D
        ≤ WithBot.some ((2 * l + 1) * Bivariate.natDegreeY (myRN N) * D) := by
  intro l hl
  obtain rfl : l = 0 := by omega
  rw [weight_β₀, myRN_natDegreeY]
  exact WithBot.coe_le_coe.mpr (by omega)

/-- The structured invariant at `k = 0` and the tight anchor `D = 2`: `Λ(β₀) = 1 ≤ 1`. -/
lemma structured_ih_zero (N : ℕ) (hH : 0 < myH.natDegree) :
    βHenselStructuredWeightInvariant (D := 2) myH 0 (myRN N) (myHypN N) hH 0 := by
  intro l hl
  obtain rfl : l = 0 := by omega
  rw [weight_β₀, myH_leadingCoeff]
  simp

/-- **`βHenselSuccTermWeightResidual` is FALSE as stated, at every `D ≥ 2`.**  On the valid
separable instance `R = Y² − 2 + u·s^N` with `N > 6D`, the loose induction hypothesis holds, yet
the `k = 0`, `i1 = 1` term has weight `N > (2·1+1)·d_R·D = 6D`. -/
theorem βHenselSuccTermWeightResidual_refuted (D : ℕ) (hD : 2 ≤ D) (N : ℕ) (hN : 6 * D < N)
    (hH : 0 < myH.natDegree) (lam : Nat.Partition (0 + 1 - 1)) :
    ¬ βHenselSuccTermWeightResidual myH 0 (myRN N) (myHypN N) hH (D := D)
        (le_trans myH_totalDegree_le hD) (myRN_two_le N) 0
        (loose_ih_zero N D hH)
        1 (by simp) lam (by simp) := by
  intro h
  unfold βHenselSuccTermWeightResidual at h
  rw [weight_term, myRN_natDegreeY] at h
  exact absurd (WithBot.coe_le_coe.mp h) (by omega)

/-- The concrete `D = 2`, `N = 13` instance of `βHenselSuccTermWeightResidual_refuted`: the term
has weight `13 > 12`. -/
theorem βHenselSuccTermWeightResidual_refuted_two
    (hH : 0 < myH.natDegree) (lam : Nat.Partition (0 + 1 - 1)) :
    ¬ βHenselSuccTermWeightResidual myH 0 (myRN 13) (myHypN 13) hH (D := 2)
        myH_totalDegree_le (myRN_two_le 13) 0
        (loose_ih_zero 13 2 hH)
        1 (by simp) lam (by simp) :=
  βHenselSuccTermWeightResidual_refuted 2 le_rfl 13 (by norm_num) hH lam

/-- **`βHenselSuccTermStructuredWeightResidual` is FALSE as stated.**  At the tight anchor
`D = 2` the structured invariant `Λ(β₀) ≤ 1` holds, yet the same term has weight `13 > 12`. -/
theorem βHenselSuccTermStructuredWeightResidual_refuted
    (hH : 0 < myH.natDegree) (lam : Nat.Partition (0 + 1 - 1)) :
    ¬ βHenselSuccTermStructuredWeightResidual myH 0 (myRN 13) (myHypN 13) hH (D := 2)
        myH_totalDegree_le (myRN_two_le 13) 0
        (structured_ih_zero 13 hH)
        1 (by simp) lam (by simp) := by
  intro h
  unfold βHenselSuccTermStructuredWeightResidual at h
  rw [weight_term, myRN_natDegreeY] at h
  exact absurd (WithBot.coe_le_coe.mp h) (by decide)

#print axioms βHenselSuccTermWeightResidual_refuted
#print axioms βHenselSuccTermWeightResidual_refuted_two
#print axioms βHenselSuccTermStructuredWeightResidual_refuted

end BCIKS20.HenselNumerator.SuccTermWitness
