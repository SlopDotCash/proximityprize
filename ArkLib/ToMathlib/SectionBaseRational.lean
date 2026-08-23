/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionFactor
import ArkLib.ToMathlib.LocalSeriesBaseRationalReading

/-!
# Issue #304 — base-rationality is structural at fiber-linear factors

The section-factor theorem (`SectionFactor.lean`) delivers a **fiber-linear** factor
(`natDegree H = 1`).  This file proves that at such factors the entire ring of regular elements
is base-rational **structurally**: the canonical representative of any `𝒪`-class has fiber
degree `< 1`, i.e. it *is* a base polynomial.

* `canonicalRep_natDegree_eq_zero_of_natDegree_eq_one` — at a fiber-linear factor the canonical
  representative is fiber-constant.
* `exists_mk_C_of_natDegree_eq_one` — **structural base-rationality of `𝒪`**: every `𝒪`-class
  is `mk (C c)` for the explicit base polynomial `c := (canonical rep).coeff 0`.
* `βHensel_eq_mk_C_of_natDegree_eq_one` — in particular every `(A.1)` numerator at a
  fiber-linear factor is the class of an explicit base polynomial — the input shape of the
  whole `LocalSeriesBaseRationalReading` chain, now with **no rationality hypothesis at all**:
  the remaining per-order content at the section factor is exactly the `ξ`-power divisibility
  of these explicit base polynomials (the localized `#138` shape, now in the UFD `F[Z]`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5, Appendix A.2/A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open scoped BigOperators

namespace ArkLib

namespace SectionBaseRational

variable {F : Type} [Field F]

/-- At a fiber-linear factor the canonical representative of any `𝒪`-class is
fiber-constant. -/
theorem canonicalRep_natDegree_eq_zero_of_natDegree_eq_one {H : F[X][Y]}
    (hH : 0 < H.natDegree) (h1 : H.natDegree = 1) (a : 𝒪 H) :
    (canonicalRepOf𝒪 hH a).natDegree = 0 := by
  have hlt := canonicalRepOf𝒪_degree_lt hH a
  have hdeg1 : (H_tilde' H).degree = 1 := by
    rw [Polynomial.degree_eq_natDegree (H_tilde'_monic H hH).ne_zero,
      natDegree_H_tilde' hH, h1]
    rfl
  rw [hdeg1] at hlt
  have hle : (canonicalRepOf𝒪 hH a).degree ≤ 0 :=
    Nat.WithBot.lt_one_iff_le_zero.mp hlt
  exact Nat.le_zero.mp (Polynomial.natDegree_le_iff_degree_le.mpr hle)

/-- **Structural base-rationality of `𝒪` at fiber-linear factors**: every class is the class of
an explicit base polynomial, `a = mk (C ((canonical rep).coeff 0))`. -/
theorem exists_mk_C_of_natDegree_eq_one {H : F[X][Y]}
    (hH : 0 < H.natDegree) (h1 : H.natDegree = 1) (a : 𝒪 H) :
    a = Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (Polynomial.C ((canonicalRepOf𝒪 hH a).coeff 0)) := by
  have hc : canonicalRepOf𝒪 hH a
      = Polynomial.C ((canonicalRepOf𝒪 hH a).coeff 0) :=
    Polynomial.eq_C_of_natDegree_le_zero
      (le_of_eq (canonicalRep_natDegree_eq_zero_of_natDegree_eq_one hH h1 a))
  rw [← hc, mk_canonicalRepOf𝒪]

/-- Every `(A.1)` numerator at a fiber-linear factor is the class of an explicit base
polynomial — the `LocalSeriesBaseRationalReading` input shape with no hypothesis. -/
theorem βHensel_eq_mk_C_of_natDegree_eq_one {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (h1 : H.natDegree = 1) {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    βHensel H x₀ R hHyp t
      = Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (Polynomial.C ((canonicalRepOf𝒪 (Fact.out) (βHensel H x₀ R hHyp t)).coeff 0)) :=
  exists_mk_C_of_natDegree_eq_one (Fact.out) h1 _

end SectionBaseRational

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.SectionBaseRational.canonicalRep_natDegree_eq_zero_of_natDegree_eq_one
#print axioms ArkLib.SectionBaseRational.exists_mk_C_of_natDegree_eq_one
#print axioms ArkLib.SectionBaseRational.βHensel_eq_mk_C_of_natDegree_eq_one
