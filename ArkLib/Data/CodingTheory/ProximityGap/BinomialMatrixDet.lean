/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Choose.Basic

/-!
# The binomial-coefficient matrix is nonsingular (#389)

For naturals `m₀, …, m_{l-1}` the binomial matrix `B_{i,a} = C(mᵢ, a)` over a field `F` satisfies the
**descPochhammer / Vandermonde identity**

  `det[ C(mᵢ, a) ]_{i,a} · ∏_{a<l} a!  =  ∏_{i<j} (mⱼ − mᵢ)`        (`det_choose_mul_prod_factorial`)

(`descPochhammer_a` is monic of degree `a`, so the column basis change `xᵃ ↦ descPochhammer_a`
turns the choose-matrix into the Vandermonde matrix up to the `∏ a!` column scaling). Hence the
binomial matrix is **nonsingular whenever the `mᵢ` are distinct in `F`** (`det_choose_ne_zero`).

## Why this is the #389-relevant brick

This is the algebraic heart of the *classical* (Hasse-derivative) Wronskian non-vanishing for
distinct-degree families: the Hasse-Wronskian of monomials `X^{mⱼ}` factors as
`X^{∑mⱼ − l(l−1)/2} · det[C(mⱼ, a)]`, so its non-vanishing in characteristic `p` is exactly the
statement here (the `mⱼ` distinct mod `p`, which the `det_choose_ne_zero` hypothesis encodes). The
classical Wronskian is the tool the Shkredov–Vyugin / Heath-Brown–Konyagin additive-shift Stepanov
argument uses for the smooth-domain additive-energy bound — the classical analogue of GK16's
already-proven *folded* Wronskian non-vanishing (`GK16Lemma12.foldedWronskian_ne_zero_of_…`).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- Entry identity: `descPochhammer F a` evaluated at a natural `m` equals `a! · C(m, a)` in `F`. -/
theorem descPochhammer_eval_nat (a m : ℕ) :
    (descPochhammer F a).eval (m : F) = (a.factorial : F) * (Nat.choose m a : F) := by
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- **The binomial matrix determinant identity.** `det[C(mᵢ, a)]_{i,a} · ∏_{a<l} a! =
∏_{i<j}(mⱼ − mᵢ)` in `F` (the Vandermonde determinant of the `(mᵢ : F)`). -/
theorem det_choose_mul_prod_factorial {l : ℕ} (m : Fin l → ℕ) :
    (Matrix.of (fun i a : Fin l => (Nat.choose (m i) a : F))).det
        * ∏ a : Fin l, ((a : ℕ).factorial : F)
      = (Matrix.vandermonde (fun i => (m i : F))).det := by
  classical
  -- The descPochhammer-evaluation matrix has det equal to the Vandermonde det
  -- (column basis change by the monic degree-`a` polynomials `descPochhammer_a`).
  have hN : (Matrix.vandermonde (fun i => (m i : F))).det
      = (Matrix.of (fun i a : Fin l => ((descPochhammer F (a : ℕ)).eval (m i : F)))).det := by
    apply det_eval_matrixOfPolynomials_eq_det_vandermonde
    · intro a; exact descPochhammer_natDegree F (a : ℕ)
    · intro a; exact monic_descPochhammer F (a : ℕ)
  -- Each entry `descPochhammer_a(mᵢ) = a! · C(mᵢ, a)`.
  have hcol : (Matrix.of (fun i a : Fin l => ((descPochhammer F (a : ℕ)).eval (m i : F))))
      = (Matrix.of (fun i a : Fin l => ((a : ℕ).factorial : F) * (Nat.choose (m i) a : F))) := by
    ext i a; simp only [Matrix.of_apply]; exact descPochhammer_eval_nat (a : ℕ) (m i)
  rw [hN, hcol]
  -- `det_mul_row v A : det (of fun i j => v j * A i j) = (∏ v) · det A` scales by the *column*
  -- index, exactly matching the `a! · C(mᵢ,a)` shape with `v a = a!`.
  have key : (Matrix.of (fun i a : Fin l => ((a : ℕ).factorial : F) * (Nat.choose (m i) a : F)))
      = Matrix.of (fun i a : Fin l => ((a : ℕ).factorial : F)
          * (Matrix.of (fun i a : Fin l => (Nat.choose (m i) a : F))) i a) := by
    ext i a; simp [Matrix.of_apply]
  rw [key, Matrix.det_mul_row]
  ring

/-- **The binomial matrix is nonsingular for distinct rows.** If the naturals `mᵢ` are distinct in
`F` (i.e. `i ↦ (mᵢ : F)` is injective — equivalently the `mᵢ` are distinct mod `char F`), then
`det[C(mᵢ, a)]_{i,a} ≠ 0`. -/
theorem det_choose_ne_zero {l : ℕ} (m : Fin l → ℕ)
    (hinj : Function.Injective (fun i => (m i : F))) :
    (Matrix.of (fun i a : Fin l => (Nat.choose (m i) a : F))).det ≠ 0 := by
  have hvand : (Matrix.vandermonde (fun i => (m i : F))).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  intro hzero
  apply hvand
  rw [← det_choose_mul_prod_factorial m, hzero, zero_mul]

end ProximityGap.BinomialDet

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.det_choose_mul_prod_factorial
#print axioms ProximityGap.BinomialDet.det_choose_ne_zero
