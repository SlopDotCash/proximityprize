/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.XiOrderInterp

/-!
# Issue #304 — `SectionXiOrder` DISSOLVES: `ξ̄` is a unit at the section factor

The last localized residual (`SectionXiOrder`, the `ξ`-power divisibility in `F[Z]`) is
**proven** at monic fiber-linear factors — not by the A.4 `+1`-bookkeeping, but because it is
trivial there: the in-tree separability hypothesis (`Hypotheses.separable_evalX`, an
`IsCoprime` in `F[Z][T]`) **evaluated along the branch section** forces the `ξ`-representative
to be a *unit* of `F[Z]`.

The mechanism: monic fiber-linear `H` has the section `s := −H.coeff 0` with `P(s) = 0`
(`H ∣ P`); mapping the coprimality `a·P + b·P′ = 1` through evaluation at `s` collapses to
`b(s)·P′(s) = 1` — so `P′(s)` is a unit; and the `ξ`-representative at the section factor
**is** `P′(s)` (monic `ξ_pre` is exactly the specialized derivative, and the canonical
representative of an `mk`-class at a fiber-linear modulus is evaluation at the section).

* `derivative_isUnit_at_section` — separability + the section ⟹ `P′(s)` is a unit.
* `xi_pre_monic_eq_derivative` — at monic `H`, `2 ≤ deg_Y R`: `ξ_pre = P′` on the nose.
* `xiRep_eq_eval_section` — the canonical `ξ`-representative content is `ξ_pre(s)`.
* `sectionXiOrder_of_monic_linear` — **the dissolution**: `SectionXiOrder` holds at every
  monic fiber-linear factor.  Combined with the branch-collapse dichotomy (only such factors
  carry the curve), the `#138`-shaped residual is CLOSED on the faithful path: the deep
  `+1`-order bookkeeping is unnecessary exactly where the §5 argument routes the proof.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5, Appendix A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open scoped BigOperators

namespace ArkLib

namespace SectionXiUnit

variable {F : Type} [Field F]

/-- Monic fiber-linear `H` vanishes at its section `s := −H.coeff 0`. -/
theorem eval_section_eq_zero {H : F[X][Y]} (hm : H.Monic) (h1 : H.natDegree = 1) :
    H.eval (-(H.coeff 0)) = 0 := by
  rw [hm.eq_X_add_C h1]
  simp

/-- **Separability is a unit-derivative at the section.**  `H ∣ P` and `P` separable force
`P′(s)` to be a unit of `F[Z]`. -/
theorem derivative_isUnit_at_section {H P : F[X][Y]} (hm : H.Monic) (h1 : H.natDegree = 1)
    (hdvd : H ∣ P) (hsep : P.Separable) :
    IsUnit ((Polynomial.derivative P).eval (-(H.coeff 0))) := by
  have hP0 : P.eval (-(H.coeff 0)) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, Polynomial.eval_mul, eval_section_eq_zero hm h1, zero_mul]
  have hco := IsCoprime.map hsep (Polynomial.evalRingHom (-(H.coeff 0)))
  simp only [Polynomial.coe_evalRingHom] at hco
  rw [hP0] at hco
  exact isCoprime_zero_left.mp hco

/-- At monic `H` with `2 ≤ deg_Y R`, the `ξ` representative polynomial is exactly the
specialized derivative: `ξ_pre = evalX (C x₀) (derivative R)`. -/
theorem xi_pre_monic_eq_derivative {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hlc : H.leadingCoeff = 1) (hd2 : 2 ≤ R.natDegree) :
    ξ_pre x₀ R H = Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R) := by
  rw [ξ_pre, if_pos hd2, hlc]
  set P' := Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R) with hP'
  have hdeg : P'.natDegree < R.natDegree := by
    have hle1 : P'.natDegree ≤ (Polynomial.derivative R).natDegree := by
      rw [hP', Bivariate.evalX_eq_map]
      exact Polynomial.natDegree_map_le
    have hle2 : (Polynomial.derivative R).natDegree ≤ R.natDegree - 1 :=
      Polynomial.natDegree_derivative_le R
    omega
  simp only [one_pow, mul_one, EuclideanDomain.div_one]
  rw [show R.natDegree - 1 = (R.natDegree - 1 - 1) + 1 from by omega]
  rw [← Finset.sum_range_succ (fun i => Polynomial.C (P'.coeff i) * Polynomial.X ^ i)]
  conv_rhs => rw [P'.as_sum_range' R.natDegree (by omega)]
  rw [show (R.natDegree - 1 - 1) + 1 + 1 = R.natDegree from by omega]
  exact Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial

/-- The canonical `ξ`-representative content at a monic fiber-linear factor is `ξ_pre`
evaluated at the section. -/
theorem xiRep_eq_eval_section {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hm : H.Monic) (h1 : H.natDegree = 1) (hHyp : Hypotheses x₀ R H) :
    (canonicalRepOf𝒪 (Fact.out) (ξ x₀ R H hHyp)).coeff 0
      = (ξ_pre x₀ R H).eval (-(H.coeff 0)) := by
  have hHt : H_tilde' H = Polynomial.X - Polynomial.C (-(H.coeff 0)) := by
    rw [H_tilde', if_neg (by omega), h1]
    rw [map_neg, sub_neg_eq_add]
    have hc1 : H.coeff 1 = 1 := by
      have := hm.coeff_natDegree
      rwa [h1] at this
    simp [Finset.sum_range_one, hc1]
  rw [canonicalRepOf𝒪]
  set p := (ξ x₀ R H hHyp).out with hp
  have hmk : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p
      = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ξ_pre x₀ R H) := by
    rw [hp, Ideal.Quotient.mk_out]
    rfl
  clear_value p
  rw [hHt, Polynomial.modByMonic_X_sub_C_eq_C_eval, Polynomial.coeff_C_zero]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, hHt] at hmk
  obtain ⟨g, hg⟩ := hmk
  have heval := congrArg (Polynomial.eval (-(H.coeff 0))) hg
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul] at heval
  exact sub_eq_zero.mp heval

/-- **THE DISSOLUTION.**  `SectionXiOrder` holds at every monic fiber-linear factor: the
`ξ`-representative is a unit (separability at the section), and units divide everything. -/
theorem sectionXiOrder_of_monic_linear {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hm : H.Monic) (h1 : H.natDegree = 1) (hd2 : 2 ≤ R.natDegree)
    (hHyp : Hypotheses x₀ R H) :
    SectionXiDivisibility.SectionXiOrder x₀ R hHyp := by
  have hunit : IsUnit ((canonicalRepOf𝒪 (Fact.out) (ξ x₀ R H hHyp)).coeff 0) := by
    rw [xiRep_eq_eval_section hm h1 hHyp, xi_pre_monic_eq_derivative hm.leadingCoeff hd2]
    rw [show Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R)
        = Polynomial.derivative (Bivariate.evalX (Polynomial.C x₀) R) from by
      rw [Bivariate.evalX_eq_map, Bivariate.evalX_eq_map, Polynomial.derivative_map]]
    exact derivative_isUnit_at_section hm h1 hHyp.dvd_evalX hHyp.separable_evalX
  exact fun t => (hunit.pow _).dvd

end SectionXiUnit

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.SectionXiUnit.eval_section_eq_zero
#print axioms ArkLib.SectionXiUnit.derivative_isUnit_at_section
#print axioms ArkLib.SectionXiUnit.xi_pre_monic_eq_derivative
#print axioms ArkLib.SectionXiUnit.xiRep_eq_eval_section
#print axioms ArkLib.SectionXiUnit.sectionXiOrder_of_monic_linear
