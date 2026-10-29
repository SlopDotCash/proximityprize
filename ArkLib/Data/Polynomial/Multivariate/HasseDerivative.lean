import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Antidiagonal

namespace ArkLib.MvPolynomial

open _root_.MvPolynomial
open Finsupp

variable {σ : Type*} {R : Type*} [CommRing R]

/-- The `taylor` ring homomorphism `P(X) ↦ P(X + Y)`.
We represent the variables `X` as the inner variables and `Y` as the outer variables.
Thus `taylor P` evaluates `P` at `X_i + Y_i`. -/
noncomputable def taylor : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ R) :=
  eval₂Hom (RingHom.comp C C) (fun i => C (X i) + X i)

/-- The Hasse derivative of `p` with respect to a multi-index `d`
is the coefficient of `Y^d` in `taylor p`. -/
noncomputable def hasseDeriv (d : σ →₀ ℕ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  (taylor p).coeff d

lemma hasseDeriv_add (d : σ →₀ ℕ) (p q : MvPolynomial σ R) :
    hasseDeriv d (p + q) = hasseDeriv d p + hasseDeriv d q := by
  simp only [hasseDeriv, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

lemma hasseDeriv_mul [DecidableEq σ] (d : σ →₀ ℕ) (p q : MvPolynomial σ R) :
    hasseDeriv d (p * q)
      = Finset.sum (Finset.antidiagonal d) (fun uv => hasseDeriv uv.1 p * hasseDeriv uv.2 q) := by
  dsimp [hasseDeriv]
  rw [map_mul, coeff_mul]

/-- We say a point `a` has multiplicity at least `m` in `p` if all Hasse derivatives
of degree `< m` evaluate to 0 at `a`. -/
def mult_ge (a : σ → R) (m : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ d : σ →₀ ℕ, (d.sum fun _ v => v) < m → eval a (hasseDeriv d p) = 0

lemma mult_ge_add (a : σ → R) (m : ℕ) (p q : MvPolynomial σ R)
    (hp : mult_ge a m p) (hq : mult_ge a m q) : mult_ge a m (p + q) := by
  intro d hd
  rw [hasseDeriv_add, map_add, hp d hd, hq d hd, add_zero]

lemma mult_ge_mul [DecidableEq σ] (a : σ → R) (m n : ℕ) (p q : MvPolynomial σ R)
    (hp : mult_ge a m p) (hq : mult_ge a n q) : mult_ge a (m + n) (p * q) := by
  intro d hd
  rw [hasseDeriv_mul, map_sum]
  apply Finset.sum_eq_zero
  intro uv huv
  rw [Finset.mem_antidiagonal] at huv
  have h_add : (uv.1 + uv.2).sum (fun _ v => v) = uv.1.sum (fun _ v => v) + uv.2.sum (fun _ v => v) := by
    apply Finsupp.sum_add_index' <;> simp
  rw [huv] at h_add
  have hd_eq : d.sum (fun _ v => v) = uv.1.sum (fun _ v => v) + uv.2.sum (fun _ v => v) := h_add
  by_cases h1 : (uv.1.sum fun _ v => v) < m
  · rw [map_mul, hp uv.1 h1, zero_mul]
  · have h2 : (uv.2.sum fun _ v => v) < n := by omega
    rw [map_mul, hq uv.2 h2, mul_zero]

end ArkLib.MvPolynomial
