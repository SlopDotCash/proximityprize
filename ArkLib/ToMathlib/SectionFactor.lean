/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BranchCollapse
import ArkLib.ToMathlib.FactorPigeonhole

/-!
# Issue #304 — THE SECTION-FACTOR THEOREM: the §5 polynomial-root factor, proven

The closing composition of the `FactorPigeonhole` branch assignment with the `BranchCollapse`
engine: **the GS interpolant has a factor with the decoded surface as a polynomial root
section.**

* `section_dvd_of_factorization` — from the interpolant factorization `Q = ∏ Hᵢ`, the
  per-good-place GS list membership `Q(z, v(z)) = 0`, the count `|s|·n ≤ |good|`, and the
  degree budget `deg (Hᵢ(Z, v)) < n` — **some factor satisfies `(T − v) ∣ Hᵢ`**.  This is the
  [BCIKS20] §5 finale (the polynomial-root factor): pigeonhole selects the factor with a large
  incidence set, and the many-roots-zero engine turns the incidences into the identical
  vanishing of `Hᵢ(Z, v(Z))`.
* `section_factor_natDegree_eq_one` — when the factors are irreducible, the section factor is
  **fiber-linear** (`natDegree Hᵢ = 1`) and is an associate of `(T − v)`: the surface `v` IS
  the factor's branch.  Combined with the dichotomy (`BranchCollapse`), the unit-lc necessity,
  and the monic transport, the selected factor carries exactly the shape the entire faithful
  producer chain consumes.

With this, the last residual core of the faithful chain — the rational-branch production — is
**proven from the GS-interpolant surface**: the honest remaining inputs of the keystone are the
GS list-membership cargo (`Q(z, v(z)) = 0` on the good set — the GS decoder's defining
property), the factorization, and the counting arithmetic.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (the polynomial-root factor), §6.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open scoped BigOperators

namespace ArkLib

namespace SectionFactor

variable {F : Type} [Field F]

/-- **THE SECTION-FACTOR THEOREM** ([BCIKS20] §5, the polynomial-root factor).  From the GS
interpolant factorization, the per-good-place list membership `Q(z, v(z)) = 0`, the pigeonhole
count, and the per-factor degree budget: some factor has the decoded surface as a polynomial
root section, `(T − v) ∣ Hᵢ`. -/
theorem section_dvd_of_factorization {ι : Type*} [DecidableEq ι] [DecidableEq F]
    {s : Finset ι} {Hf : ι → F[X][Y]} {Q : F[X][Y]}
    (hQ : Q = ∏ i ∈ s, Hf i) (hsne : s.Nonempty)
    {v : F[X]} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet, Polynomial.evalEval z (v.eval z) Q = 0)
    {n : ℕ} (hcount : s.card * n ≤ goodSet.card)
    (hbudget : ∀ i ∈ s, (Polynomial.eval v (Hf i)).natDegree < n) :
    ∃ i ∈ s, (Polynomial.X - Polynomial.C v) ∣ Hf i := by
  obtain ⟨i, hi, M, _, hMcard, hMvan⟩ :=
    FactorPigeonhole.matching_supply_of_factorization hQ hsne hvan hcount
  refine ⟨i, hi, ?_⟩
  rw [Polynomial.dvd_iff_isRoot]
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ M (fun z hz => ?_)
    (lt_of_lt_of_le (hbudget i hi) hMcard)
  rw [BranchCollapse.eval_eval_eq_evalEval]
  exact hMvan z hz

/-- **Fiber-linearity of the section factor.**  When the factors are irreducible, the selected
section factor has `natDegree = 1`: the decoded surface IS the factor's branch (the factor is
an associate of `T − v`). -/
theorem section_factor_natDegree_eq_one {ι : Type*} [DecidableEq ι] [DecidableEq F]
    {s : Finset ι} {Hf : ι → F[X][Y]} {Q : F[X][Y]}
    (hQ : Q = ∏ i ∈ s, Hf i) (hsne : s.Nonempty)
    (hirr : ∀ i ∈ s, Irreducible (Hf i))
    {v : F[X]} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet, Polynomial.evalEval z (v.eval z) Q = 0)
    {n : ℕ} (hcount : s.card * n ≤ goodSet.card)
    (hbudget : ∀ i ∈ s, (Polynomial.eval v (Hf i)).natDegree < n) :
    ∃ i ∈ s, (Hf i).natDegree = 1 ∧ (Polynomial.X - Polynomial.C v) ∣ Hf i := by
  obtain ⟨i, hi, hdvd⟩ := section_dvd_of_factorization hQ hsne hvan hcount hbudget
  refine ⟨i, hi, ?_, hdvd⟩
  obtain ⟨q, hq⟩ := hdvd
  have hXv : ¬ IsUnit (Polynomial.X - Polynomial.C v) := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at this
    omega
  rcases ((hirr i hi).isUnit_or_isUnit hq).resolve_left hXv with hqu
  have hq0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hqu
  have hXv0 : (Polynomial.X - Polynomial.C v) ≠ 0 := by
    intro h0
    have := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_zero] at this
    omega
  have hqne : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq
    exact (hirr i hi).ne_zero hq
  rw [hq, Polynomial.natDegree_mul hXv0 hqne, Polynomial.natDegree_X_sub_C, hq0]

end SectionFactor

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.SectionFactor.section_dvd_of_factorization
#print axioms ArkLib.SectionFactor.section_factor_natDegree_eq_one
