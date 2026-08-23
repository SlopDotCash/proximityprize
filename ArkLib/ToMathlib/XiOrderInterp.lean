/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionXiDivisibility

/-!
# Issue #304 — `SectionXiOrder` from reading interpolation (the closing equivalence)

The localized residual `SectionXiOrder` (the `ξ`-power divisibility in `F[Z]`) is **equivalent**
to the §5 conclusion shape at the section factor: the per-place readings
`β̄ₜ(z)/ξ̄(z)^{2t−1}` interpolating a polynomial on more places than the degree budget.

* `xi_pow_dvd_of_interpolation` — **the production**: if at every place of a large enough set
  (with `ξ̄` nonvanishing there) the numerator value factors through a polynomial interpolant —
  `β̄ₜ(z) = cₜ(z)·ξ̄(z)^{2t−1}` — then the divisibility holds **globally**:
  `ξ̄^{2t−1} ∣ β̄ₜ` in `F[Z]` (the counting engine turns pointwise clearing into identical
  equality).

Composed with `factored_iff_xi_pow_dvd` and the universal Hensel pin (whose readings at good
places ARE the decoded coefficients `(P z).coeff t`), this closes the formal circle: at the
section factor, the keystone conclusion, the factored forms, and `SectionXiOrder` are one and
the same statement up to proven equivalences — the production of any one of them from the
per-`(u, P)` GS data produces them all.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5, Appendix A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial

namespace ArkLib

namespace SectionXiDivisibility

variable {F : Type} [Field F]

/-- **Global divisibility from pointwise interpolation.**  If on a set `S` larger than the
degree budget the numerator values clear through a polynomial interpolant —
`β(z) = c(z)·ξ(z)^{e}` for all `z ∈ S` — then `ξ^e ∣ β` identically in `F[X]`. -/
theorem xi_pow_dvd_of_interpolation {β ξc c : F[X]} {e : ℕ} {S : Finset F}
    (hread : ∀ z ∈ S, β.eval z = c.eval z * (ξc.eval z) ^ e)
    (hcard : max β.natDegree (c * ξc ^ e).natDegree < S.card) :
    ξc ^ e ∣ β := by
  have heq : β = c * ξc ^ e := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' β (c * ξc ^ e) S
      (fun z hz => ?_) hcard
    rw [hread z hz, Polynomial.eval_mul, Polynomial.eval_pow]
  exact ⟨c, by rw [heq]; ring⟩

end SectionXiDivisibility

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.SectionXiDivisibility.xi_pow_dvd_of_interpolation
