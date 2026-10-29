import Mathlib
import ArkLib.Data.CodingTheory.GuruswamiSudan.MultiplicityInterpolation

/-! # Coefficient-vector ↔ bivariate-polynomial dictionary (foundation)

The GS multiplicity interpolation (`GSMultInterp`) works with an abstract coefficient vector
`c : CoeffSpace k D` and a self-contained binomial `hasseCoeff`. To feed its output into the
`F[X][Y]` interpolant `Q` consumed downstream, one needs the dictionary `c ↦ Q`. This file
provides its foundation: the explicit map `toPoly` and the verified coefficient-extraction lemma
`toPoly_coeff`.

The remaining crux of the full dictionary — matching `GSMultInterp.hasseCoeff k D c a b` to the
`Polynomial`-side bivariate Hasse derivative of `toPoly c` for *all* orders `(a,b)` (hence
`GSMultInterp.vanishesToOrder ↔ ArkLib.GS.vanishesToOrder`) — is the order-`(a,b)` Hasse
correspondence, left for the focused follow-up. The order-`(0,0)` case is plain evaluation
(`hasseCoeff_zero_zero`). -/

open Polynomial

namespace GSMultInterp

variable {F : Type} [Field F] [DecidableEq F]

/-- The bivariate polynomial `∑_{(s,t)∈monoIdx} c(s,t)·X^s·Y^t` carried by a coefficient vector
`c`, as an element of `F[X][Y] = Polynomial (Polynomial F)` (outer variable `Y`, inner `X`). -/
noncomputable def toPoly (k D : ℕ) (c : CoeffSpace (F := F) k D) : Polynomial (Polynomial F) :=
  ∑ st : {ab : ℕ × ℕ // ab ∈ monoIdx k D},
    Polynomial.monomial st.1.2 (Polynomial.monomial st.1.1 (c st))

/-- **Coefficient extraction.** The `(s,t)`-bidegree coefficient of `toPoly c` (the `Y`-degree-`t`,
`X`-degree-`s` coefficient) is exactly the entry `c(s,t)` for `(s,t) ∈ monoIdx k D`. -/
theorem toPoly_coeff (k D : ℕ) (c : CoeffSpace (F := F) k D)
    (st : {ab : ℕ × ℕ // ab ∈ monoIdx k D}) :
    ((toPoly k D c).coeff st.1.2).coeff st.1.1 = c st := by
  classical
  rw [toPoly, Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single st]
  · simp [Polynomial.coeff_monomial]
  · intro st' _ hne
    rcases eq_or_ne st'.1.2 st.1.2 with h2 | h2
    · rcases eq_or_ne st'.1.1 st.1.1 with h1 | h1
      · exact absurd (Subtype.ext (Prod.ext h1 h2)) hne
      · simp [Polynomial.coeff_monomial, h2, h1]
    · simp [Polynomial.coeff_monomial, h2]
  · intro h; exact absurd (Finset.mem_univ st) h

/-- `toPoly` is additive in the coefficient vector. -/
theorem toPoly_add (k D : ℕ) (c c' : CoeffSpace (F := F) k D) :
    toPoly k D (c + c') = toPoly k D c + toPoly k D c' := by
  simp only [toPoly, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun st _ => ?_)
  simp only [map_add]

/-- **Base-case Hasse correspondence (order `(0,0)`).** The bivariate evaluation of `toPoly c`
at `(x₀, y₀)` equals the order-`(0,0)` Hasse coefficient (plain evaluation). This anchors the
`GSMultInterp.hasseCoeff ↔ Polynomial`-side bivariate-Hasse dictionary at the root condition; the
general order-`(a,b)` case is the remaining crux. -/
theorem toPoly_eval (k D : ℕ) (c : CoeffSpace (F := F) k D) (x₀ y₀ : F) :
    ((toPoly k D c).eval (Polynomial.C y₀)).eval x₀ = hasseCoeff k D c 0 0 x₀ y₀ := by
  rw [hasseCoeff_zero_zero, toPoly, Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun st _ => ?_)
  simp [Polynomial.eval_monomial, Polynomial.eval_pow, mul_assoc]

#print axioms GSMultInterp.toPoly_coeff
#print axioms GSMultInterp.toPoly_add
#print axioms GSMultInterp.toPoly_eval

end GSMultInterp
