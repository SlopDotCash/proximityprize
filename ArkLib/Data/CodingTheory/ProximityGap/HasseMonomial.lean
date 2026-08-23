/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BivariateVanishing

/-! Single-monomial bivariate Hasse coefficient — the crux of the coefficient-vector ↔
bivariate-polynomial dictionary. By linearity this extends to `toPoly c` and matches
`GSMultInterp.hasseCoeff`. -/

open Polynomial

namespace ArkLib.GS

variable {F : Type} [CommRing F]

/-- The bivariate Hasse coefficient of the monomial `X^s · Y^t · p` at order `(i,j)`, evaluated
at `(x₀, y₀)`, is `(s choose i)(t choose j)·p·x₀^{s-i}·y₀^{t-j}`. -/
theorem hasseCoeff_monomial (i j s t : ℕ) (p x₀ y₀ : F) :
    hasseCoeff i j (Polynomial.monomial t (Polynomial.monomial s p)) x₀ y₀
      = (s.choose i : F) * (t.choose j : F) * p * x₀ ^ (s - i) * y₀ ^ (t - j) := by
  rw [hasseCoeff, innerTaylorCoeff, Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial,
      Polynomial.eval_monomial]
  have hmid : ((t.choose j : Polynomial F) * Polynomial.monomial s p) * (Polynomial.C y₀) ^ (t - j)
      = Polynomial.monomial s ((t.choose j : F) * p * y₀ ^ (t - j)) := by
    rw [← Polynomial.C_pow, mul_assoc, Polynomial.monomial_mul_C,
        show (t.choose j : Polynomial F) = Polynomial.C (t.choose j : F) from
          (Polynomial.C_eq_natCast _).symm, Polynomial.C_mul_monomial]
    congr 1
    ring
  rw [hmid, Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  push_cast
  ring

end ArkLib.GS
