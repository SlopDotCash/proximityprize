/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Team
-/
import ArkLib.Data.Polynomial.Multivariate.HasseDerivative
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div

/-!
# Substitution–multiplicity transfer (Guruswami–Sudan companion)

If a bivariate `Q(X,Y)` has Hasse-multiplicity `≥ m` at `(x, f x)`, then the univariate
substitution `P(T) = Q(T, f(T))` has a root of multiplicity `≥ m` at `x` — **provided `P ≠ 0`**.

The `P ≠ 0` hypothesis is essential: for `Q = X₀ − X₁`, `f = X` one has `P = T − T = 0`, and
`rootMultiplicity x 0 = 0`, so the statement without it (the older `rootMultiplicity_aeval_ge`)
is false. This is the companion to `gkl24_interpolation_existence`; together they are the two
halves of the Guruswami–Sudan list-decoding argument.

Proof outline. Write `R := Q(X + (x, f x))`, the bivariate Taylor shift. The Hasse-multiplicity
hypothesis says every monomial of `R` has total degree `≥ m` (Lemma
`coeff_shift_eq_eval_hasseDeriv`). The substitution factors as `taylor x P = Θ R` for an
`F`-algebra map `Θ` sending `X₀ ↦ T` and `X₁ ↦ w` with `T ∣ w`; hence `Θ` sends every monomial of
`R` (degree `≥ m`) to a multiple of `Tᵐ`, so `Tᵐ ∣ taylor x P`, i.e. `(T − x)ᵐ ∣ P`.
-/

open MvPolynomial
open _root_.ArkLib.MvPolynomial
open scoped BigOperators

namespace CodingTheory.Bounds

variable {F : Type} [Field F]

/-- **Hasse–shift identity.** The `X^d`-coefficient of the bivariate Taylor shift
`Q(X + p)` equals the value at `p` of the `d`-th Hasse derivative of `Q`. -/
lemma coeff_shift_eq_eval_hasseDeriv (p : Fin 2 → F) (Q : MvPolynomial (Fin 2) F)
    (d : Fin 2 →₀ ℕ) :
    coeff d (aeval (fun i => X i + C (p i)) Q) = eval p (hasseDeriv d Q) := by
  have hmap : MvPolynomial.map (eval p) (taylor Q) = aeval (fun i => X i + C (p i)) Q := by
    have h : (MvPolynomial.map (eval p)).comp taylor
        = (aeval (fun i => X i + C (p i)) : MvPolynomial (Fin 2) F →ₐ[F] _).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [taylor, eval₂Hom_C, MvPolynomial.map_C, eval_C, RingHom.comp_apply]
      · intro i
        simp [taylor, eval₂Hom_X, map_add, MvPolynomial.map_C, MvPolynomial.map_X,
          eval_X, add_comm, RingHom.comp_apply]
    calc MvPolynomial.map (eval p) (taylor Q)
        = ((MvPolynomial.map (eval p)).comp taylor) Q := rfl
      _ = (aeval (fun i => X i + C (p i))).toRingHom Q := by rw [h]
      _ = aeval (fun i => X i + C (p i)) Q := rfl
  rw [← hmap, MvPolynomial.coeff_map]
  rfl

/-- A `Fin 2 →₀ ℕ` multi-index has total degree equal to the sum of its two values. -/
private lemma fin2_sum (d : Fin 2 →₀ ℕ) : (d.sum fun _ e => e) = d 0 + d 1 := by
  rw [Finsupp.sum_fintype]
  · exact Fin.sum_univ_two _
  · intro _; rfl

/-- **Substitution–multiplicity transfer** (the corrected `rootMultiplicity_aeval_ge`).
If `Q` has Hasse multiplicity `≥ m` at `(x, f x)` and the substitution `P = Q(T, f(T))` is
nonzero, then `x` is a root of `P` of multiplicity `≥ m`. -/
theorem rootMultiplicity_aeval_ge
    (Q : MvPolynomial (Fin 2) F) (f : Polynomial F) (x : F) (m : ℕ)
    (hP : (aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q) ≠ 0)
    (h_mult : ArkLib.MvPolynomial.mult_ge ![x, f.eval x] m Q) :
    m ≤ Polynomial.rootMultiplicity x
      (aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q) := by
  classical
  set v : Fin 2 → Polynomial F := fun i => if i = 0 then Polynomial.X else f with hv
  set P : Polynomial F := aeval v Q with hPdef
  rw [Polynomial.le_rootMultiplicity_iff hP]
  -- `w := f(T + x) − C (f x)` is divisible by `T`.
  set w : Polynomial F := f.comp (Polynomial.X + Polynomial.C x) - Polynomial.C (f.eval x) with hw
  have hXw : (Polynomial.X : Polynomial F) ∣ w := by
    rw [Polynomial.X_dvd_iff, hw]
    simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  -- `Θ : MvPoly (Fin 2) F →ₐ Poly F`, `X₀ ↦ T`, `X₁ ↦ w`.
  set Θ : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
    aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else w) with hΘ
  set point : Fin 2 → F := ![x, f.eval x] with hpoint
  -- `R := Q(X + point)`, the bivariate Taylor shift.
  set R : MvPolynomial (Fin 2) F := aeval (fun i => X i + C (point i)) Q with hR
  -- Factorisation `Θ R = taylor x P`.
  have hfact : Θ R = Polynomial.taylor x P := by
    have hL : Θ R = aeval (fun i => Θ (X i + C (point i))) Q := by
      rw [hR, comp_aeval_apply]
    have hRr : Polynomial.taylor x P
        = aeval (fun i => Polynomial.aeval (Polynomial.X + Polynomial.C x) (v i)) Q := by
      rw [hPdef, Polynomial.taylor_apply, Polynomial.comp_eq_aeval, comp_aeval_apply]
    rw [hL, hRr]
    refine congrArg (fun g => aeval g Q) ?_
    funext i
    fin_cases i
    · simp [hΘ, hv, hpoint]
    · simp [hΘ, hv, hpoint, hw, Polynomial.comp_eq_aeval]
  -- Heart: `Tᵐ ∣ Θ R`.
  have hXmR : (Polynomial.X : Polynomial F) ^ m ∣ Θ R := by
    have hΘR : Θ R = ∑ d ∈ R.support, Θ (monomial d (coeff d R)) := by
      conv_lhs => rw [R.as_sum]
      rw [map_sum]
    rw [hΘR]
    apply Finset.dvd_sum
    intro d hd
    have hcoeff : coeff d R ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have hdeg : m ≤ d 0 + d 1 := by
      by_contra hlt
      push_neg at hlt
      refine hcoeff ?_
      rw [hR, coeff_shift_eq_eval_hasseDeriv]
      exact h_mult d (by rw [fin2_sum]; omega)
    rw [hΘ, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp),
      Fin.prod_univ_two]
    -- goal: Tᵐ ∣ algebraMap _ _ (coeff d R) * (g 0 ^ d 0 * g 1 ^ d 1)
    refine Dvd.dvd.mul_left ?_ _
    show (Polynomial.X : Polynomial F) ^ m ∣ Polynomial.X ^ (d 0) * w ^ (d 1)
    have h1 : (Polynomial.X : Polynomial F) ^ (d 0) * Polynomial.X ^ (d 1)
        ∣ Polynomial.X ^ (d 0) * w ^ (d 1) :=
      mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hXw (d 1))
    have h2 : (Polynomial.X : Polynomial F) ^ m
        ∣ Polynomial.X ^ (d 0) * Polynomial.X ^ (d 1) := by
      rw [← pow_add]; exact pow_dvd_pow _ hdeg
    exact h2.trans h1
  -- Transfer `Tᵐ ∣ taylor x P` back to `(T − x)ᵐ ∣ P`.
  rw [hfact] at hXmR
  have hcomp : Polynomial.aeval (Polynomial.X - Polynomial.C x) (Polynomial.taylor x P) = P := by
    rw [Polynomial.taylor_apply, ← Polynomial.comp_eq_aeval, Polynomial.comp_assoc]
    simp [Polynomial.add_comp]
  have hkey := map_dvd (Polynomial.aeval (Polynomial.X - Polynomial.C x) :
      Polynomial F →ₐ[F] Polynomial F) hXmR
  rw [map_pow, Polynomial.aeval_X, hcomp] at hkey
  exact hkey

end CodingTheory.Bounds
