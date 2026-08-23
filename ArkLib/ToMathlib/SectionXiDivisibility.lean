/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionBaseRational

/-!
# Issue #304 — the localized `ξ`-order: the last per-order item as a plain `F[Z]`-divisibility

At the section factor (`natDegree H = 1`) the last per-order wiring item — the factored form
`βHensel t = mk (C c′ₜ) · ξ^{2t−1}` that the reading chain divides by — reduces to a **plain
polynomial divisibility in `F[Z]`**:

* `mk_C_injective_of_natDegree_eq_one` — `mk ∘ C` is injective at fiber-linear factors (a
  monic fiber-linear polynomial cannot divide a nonzero fiber-constant).
* `factored_iff_xi_pow_dvd` — the factored form holds **iff**
  `(ξ-rep)^{2t−1} ∣ (βHensel-rep)` in `F[Z]`, where both representatives are the explicit
  fiber-constant contents of `SectionBaseRational`.  The deep `#138` Newton `ξ`-order content
  is therefore, at the section factor, exactly the named `SectionXiOrder` divisibility family —
  concrete polynomial division in a UFD, with no quotient-ring or function-field content left.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  Appendix A.4 (Claim A.2, the `ξ`-order gain).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open scoped BigOperators

namespace ArkLib

namespace SectionXiDivisibility

variable {F : Type} [Field F]

/-- At a fiber-linear factor, `mk ∘ C` is injective: a monic fiber-linear polynomial cannot
divide a nonzero fiber-constant. -/
theorem mk_C_injective_of_natDegree_eq_one {H : F[X][Y]}
    (hH : 0 < H.natDegree) (h1 : H.natDegree = 1) {a b : F[X]}
    (h : Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C a)
      = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C b)) :
    a = b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨q, hq⟩ := h
  rcases eq_or_ne q 0 with hq0 | hq0
  · rw [hq0, mul_zero] at hq
    exact Polynomial.C_injective (sub_eq_zero.mp hq)
  · exfalso
    have hdeg : (H_tilde' H).natDegree = 1 := by rw [natDegree_H_tilde' hH, h1]
    have hne : H_tilde' H ≠ 0 := (H_tilde'_monic H hH).ne_zero
    have hCne : Polynomial.C a - Polynomial.C b ≠ 0 := by
      intro h0
      rw [h0] at hq
      exact hq0 (by
        rcases mul_eq_zero.mp hq.symm with h | h
        · exact absurd h hne
        · exact h)
    have hd := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hne hq0, hdeg, ← map_sub, Polynomial.natDegree_C] at hd
    omega

/-- **The localized `ξ`-order reduction.**  At a fiber-linear factor the factored form
`βHensel t = mk (C c′) · ξ^{2t−1}` holds for some `c′` **iff** the explicit fiber-constant
representative of `ξ`, raised to the `2t−1`, divides that of `βHensel t` — a plain divisibility
in `F[Z]`. -/
theorem factored_iff_xi_pow_dvd {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (h1 : H.natDegree = 1) {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) (t : ℕ) :
    (∃ c' : F[X], βHensel H x₀ R hHyp t
        = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C c')
          * (ξ x₀ R H hHyp) ^ (2 * t - 1))
      ↔ ((canonicalRepOf𝒪 (Fact.out) (ξ x₀ R H hHyp)).coeff 0) ^ (2 * t - 1)
          ∣ (canonicalRepOf𝒪 (Fact.out) (βHensel H x₀ R hHyp t)).coeff 0 := by
  have hβ := SectionBaseRational.βHensel_eq_mk_C_of_natDegree_eq_one h1 hHyp t
  have hξ := SectionBaseRational.exists_mk_C_of_natDegree_eq_one
    (Fact.out) h1 (ξ x₀ R H hHyp)
  constructor
  · rintro ⟨c', hc'⟩
    have hmk : Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (Polynomial.C ((canonicalRepOf𝒪 (Fact.out) (βHensel H x₀ R hHyp t)).coeff 0))
        = Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (Polynomial.C (c' * ((canonicalRepOf𝒪 (Fact.out) (ξ x₀ R H hHyp)).coeff 0)
            ^ (2 * t - 1))) := by
      rw [← hβ, hc']
      nth_rewrite 1 [hξ]
      rw [← map_pow, ← map_mul, ← Polynomial.C_pow, ← Polynomial.C_mul]
    have heq := mk_C_injective_of_natDegree_eq_one (Fact.out) h1 hmk
    exact ⟨c', by rw [heq]; ring⟩
  · rintro ⟨c', hc'⟩
    refine ⟨c', ?_⟩
    rw [hβ, hc', Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow, ← hξ]
    ring

/-- **The named localized residual** (`SectionXiOrder`): the `ξ`-power divisibility family of
the explicit fiber-constant representatives — the `#138` Newton `ξ`-order content at the
section factor, as a plain `F[Z]`-divisibility. -/
def SectionXiOrder {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ, ((canonicalRepOf𝒪 (Fact.out) (ξ x₀ R H hHyp)).coeff 0) ^ (2 * t - 1)
    ∣ (canonicalRepOf𝒪 (Fact.out) (βHensel H x₀ R hHyp t)).coeff 0

/-- The factored forms at every order from the named residual. -/
theorem factored_of_sectionXiOrder {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (h1 : H.natDegree = 1) {x₀ : F} {R : F[X][X][Y]} {hHyp : Hypotheses x₀ R H}
    (hxi : SectionXiOrder x₀ R hHyp) (t : ℕ) :
    ∃ c' : F[X], βHensel H x₀ R hHyp t
      = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C c')
        * (ξ x₀ R H hHyp) ^ (2 * t - 1) :=
  (factored_iff_xi_pow_dvd h1 hHyp t).mpr (hxi t)

end SectionXiDivisibility

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.SectionXiDivisibility.mk_C_injective_of_natDegree_eq_one
#print axioms ArkLib.SectionXiDivisibility.factored_iff_xi_pow_dvd
#print axioms ArkLib.SectionXiDivisibility.factored_of_sectionXiOrder
