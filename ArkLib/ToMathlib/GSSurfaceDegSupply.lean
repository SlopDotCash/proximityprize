/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceKeystone

/-!
# Issue #304 — the `hdegc` supply of `GSSurfaceData` from `Λ`-weight bounds

At the section divisor the `Λ`-grading collapses: the canonical representative of any
`𝒪`-class is fiber-constant, so its `Λ`-weight **is** the `Z`-degree of its content
(`weight_Λ_over_𝒪_section_eq_natDegree_content`).  Consequently the `hdegc` field of the
keystone bundle (degree bounds on the explicit curve coefficients) follows from per-order
`Λ`-weight bounds on the `(A.1)` numerators
(`natDegree_sectionCurveCoeff_lt_of_weight_lt`) — the exact [BCIKS20] Claim-5.8 weight shape
the §5 matching argument supplies.  The `ξ`-content division is degree-neutral (the content
is a unit).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open scoped BigOperators

namespace ArkLib

namespace GSSurfaceKeystone

variable {F : Type} [Field F]
variable {x₀ : F} {R : F[X][X][Y]} {v : F[X]}

/-- **The `Λ`-weight collapse at the section divisor**: the weight of an `𝒪`-class with
nonzero content is exactly the `Z`-degree of its (fiber-constant) content. -/
theorem weight_Λ_over_𝒪_section_eq_natDegree_content
    (a : 𝒪 (Polynomial.X - Polynomial.C v : F[X][Y])) (D : ℕ)
    (hc : (canonicalRepOf𝒪 (Fact.out) a).coeff 0 ≠ 0) :
    weight_Λ_over_𝒪 (Fact.out) a D
      = (((canonicalRepOf𝒪 (Fact.out) a).coeff 0).natDegree : WithBot ℕ) := by
  have h0 : (canonicalRepOf𝒪 (Fact.out) a).natDegree = 0 :=
    SectionBaseRational.canonicalRep_natDegree_eq_zero_of_natDegree_eq_one
      (Fact.out) (sectionH_natDegree v) a
  have hC : canonicalRepOf𝒪 (Fact.out) a
      = Polynomial.C ((canonicalRepOf𝒪 (Fact.out) a).coeff 0) :=
    Polynomial.eq_C_of_natDegree_le_zero (le_of_eq h0)
  rw [weight_Λ_over_𝒪]
  conv_lhs => rw [hC]
  rw [weight_Λ, Polynomial.support_C hc, Finset.sup_singleton]
  simp only [zero_mul, zero_add, Polynomial.coeff_C_zero]
  rfl

/-- **The `hdegc` field of `GSSurfaceData`, from per-order `Λ`-weight bounds** (the
[BCIKS20] Claim-5.8 shape): if every `(A.1)` numerator below order `n` has weight `< n`,
the explicit curve coefficients have degree `< n` — the `ξ`-content division is
degree-neutral. -/
theorem natDegree_sectionCurveCoeff_lt_of_weight_lt
    [Fact (Irreducible (Polynomial.X - Polynomial.C v : F[X][Y]))]
    [Fact (0 < (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree)]
    (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    (hd2 : 2 ≤ R.natDegree) {n D : ℕ} (hn : 0 < n)
    (hw : ∀ t < n, weight_Λ_over_𝒪 (Fact.out)
      (βHensel (Polynomial.X - Polynomial.C v) x₀ R hHyp t) D < (n : WithBot ℕ)) :
    ∀ t < n, (sectionCurveCoeff hHyp t).natDegree < n := by
  intro t ht
  rcases eq_or_ne ((canonicalRepOf𝒪 (Fact.out)
      (βHensel (Polynomial.X - Polynomial.C v) x₀ R hHyp t)).coeff 0) 0 with h0 | h0
  · have hz : sectionCurveCoeff hHyp t = 0 := by
      unfold sectionCurveCoeff
      rw [h0, EuclideanDomain.zero_div]
    rw [hz]
    simpa using hn
  · have hwt := hw t ht
    rw [weight_Λ_over_𝒪_section_eq_natDegree_content _ _ h0] at hwt
    have hdc : ((canonicalRepOf𝒪 (Fact.out)
        (βHensel (Polynomial.X - Polynomial.C v) x₀ R hHyp t)).coeff 0).natDegree < n :=
      WithBot.coe_lt_coe.mp hwt
    have huu : IsUnit ((canonicalRepOf𝒪 (Fact.out)
        (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)).coeff 0) :=
      xiContent_isUnit hHyp hd2
    have hdvd := SectionXiUnit.sectionXiOrder_of_monic_linear (sectionH_monic v)
      (sectionH_natDegree v) hd2 hHyp t
    have hueq : (canonicalRepOf𝒪 (Fact.out)
        (βHensel (Polynomial.X - Polynomial.C v) x₀ R hHyp t)).coeff 0
        = ((canonicalRepOf𝒪 (Fact.out)
            (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)).coeff 0) ^ (2 * t - 1)
          * sectionCurveCoeff hHyp t :=
      (EuclideanDomain.mul_div_cancel' (pow_ne_zero _ huu.ne_zero) hdvd).symm
    rcases eq_or_ne (sectionCurveCoeff hHyp t) 0 with hq0 | hq0
    · rw [hq0]
      simpa using hn
    · have hdeg := congrArg Polynomial.natDegree hueq
      rw [Polynomial.natDegree_mul (pow_ne_zero _ huu.ne_zero) hq0,
        Polynomial.natDegree_pow, Polynomial.natDegree_eq_zero_of_isUnit huu] at hdeg
      omega

end GSSurfaceKeystone

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.GSSurfaceKeystone.weight_Λ_over_𝒪_section_eq_natDegree_content
#print axioms ArkLib.GSSurfaceKeystone.natDegree_sectionCurveCoeff_lt_of_weight_lt
