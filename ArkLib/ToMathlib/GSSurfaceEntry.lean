/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceKeystone

/-!
# Issue #304 — the factorization-level entry of `GSSurfaceData`

Shrinks the keystone bundle's section fields to GS-factorization facts:

* `eq_section_of_monic_natDegree_one` — any monic fiber-linear factor IS a section divisor
  (`H = T − C (−H.coeff 0)`), so `(v, hdvd)` are derivable from a normalized factor.
* `section_dvd_evalX_of_factorization` — **the §6 pigeonhole entry**: a factorization of the
  specialized surface + per-place curve membership + the counting budget produce
  `(T − C v) ∣ evalX (C x₀) R` directly (`SectionFactor.section_dvd_of_factorization`
  composed through the product) — no monicity or normalization assumptions on the factors.

With these, the `hdvd` field of `GSSurfaceData` is supplied by the §5/§6 construction output
(factorization + membership + counting) rather than assumed.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5–§6.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open scoped BigOperators

namespace ArkLib

namespace GSSurfaceKeystone

variable {F : Type} [Field F]

/-- Any monic fiber-linear factor IS a section divisor. -/
theorem eq_section_of_monic_natDegree_one {H : F[X][Y]} (hm : H.Monic) (h1 : H.natDegree = 1) :
    H = Polynomial.X - Polynomial.C (-(H.coeff 0)) := by
  conv_lhs => rw [hm.eq_X_add_C h1]
  rw [map_neg, sub_neg_eq_add]

/-- The section + divisibility from any monic fiber-linear factor of the specialized
surface. -/
theorem section_dvd_evalX_of_factor {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hm : H.Monic) (h1 : H.natDegree = 1)
    (hdvd : H ∣ Bivariate.evalX (Polynomial.C x₀) R) :
    (Polynomial.X - Polynomial.C (-(H.coeff 0)) : F[X][Y])
      ∣ Bivariate.evalX (Polynomial.C x₀) R :=
  (eq_section_of_monic_natDegree_one hm h1) ▸ hdvd

/-- **The §6 pigeonhole entry**: a factorization of the specialized surface, per-place curve
membership, and the counting budget produce the section divisibility directly — no
normalization assumptions on the factors. -/
theorem section_dvd_evalX_of_factorization {κ : Type} [DecidableEq κ] [DecidableEq F]
    {x₀ : F} {R : F[X][X][Y]} {s : Finset κ} {Hf : κ → F[X][Y]}
    (hQ : Bivariate.evalX (Polynomial.C x₀) R = ∏ i ∈ s, Hf i)
    (hsne : s.Nonempty) {v : F[X]} {goodSet : Finset F}
    (hvan : ∀ z ∈ goodSet,
      Polynomial.evalEval z (v.eval z) (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    {n : ℕ} (hcount : s.card * n ≤ goodSet.card)
    (hbudget : ∀ i ∈ s, (Polynomial.eval v (Hf i)).natDegree < n) :
    (Polynomial.X - Polynomial.C v : F[X][Y]) ∣ Bivariate.evalX (Polynomial.C x₀) R := by
  obtain ⟨i, hi, hdvd⟩ :=
    SectionFactor.section_dvd_of_factorization hQ hsne hvan hcount hbudget
  exact hdvd.trans (hQ ▸ Finset.dvd_prod_of_mem Hf hi)

end GSSurfaceKeystone

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.GSSurfaceKeystone.eq_section_of_monic_natDegree_one
#print axioms ArkLib.GSSurfaceKeystone.section_dvd_evalX_of_factor
#print axioms ArkLib.GSSurfaceKeystone.section_dvd_evalX_of_factorization
