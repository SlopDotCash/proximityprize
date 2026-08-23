/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Lovett's GM-MDS proof: the substitution-divisibility kernel (Lemma 2.5) (#389)

The algebraic crux at the bottom of page 9 of Lovett (arXiv:1803.02523), in the proof of
Lemma 2.5.  After substituting `a_{n-1}` for `a_n` in a dependence `Σ wᵢₑ pᵢₑ = 0`, one obtains
`Σ w'ᵢₑ p'ᵢₑ = 0`; the independence of `P(k, V')` forces every `w'ᵢₑ ≡ 0`, i.e.

> `wᵢₑ(a₁,…,a_{n-1}, a_{n-1}) ≡ 0`,

and the conclusion is that `(a_{n-1} − a_n)` divides every `wᵢₑ`.

This file proves the underlying *general* algebra fact, stated for any commutative ring `F` and
any two indeterminates `p ≠ q` of `MvPolynomial σ F`:

* `sub_X_dvd_sub_subst` — `(Xₚ − X_q)` divides `w − ψ w`, where `ψ` is the substitution
  `Xₚ ↦ X_q` (identity elsewhere).
* `sub_X_dvd_of_subst_eq_zero` — if `ψ w = 0` then `(Xₚ − X_q) ∣ w` (the form used in Lemma 2.5,
  with `ψ = a_n ↦ a_{n-1}`: a polynomial killed by the merge substitution is divisible by the
  difference of the two merged variables).

These are the *contradiction with common-factor-freeness*: if `(Xₚ − X_q)` divided **every**
`wᵢₑ` they would all share the irreducible factor `Xₚ − X_q`, contradicting the minimal choice
of a common-factor-free dependence.

Issue #389.
-/

open MvPolynomial

namespace ArkLib.GMMDS

variable {F : Type*} [CommRing F] {σ : Type*} [DecidableEq σ]

/-- The merge substitution `Xₚ ↦ X_q`, identity on every other variable, as an `F`-algebra
endomorphism of `MvPolynomial σ F`. -/
noncomputable def substVar (p q : σ) : MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  aeval (fun s => if s = p then (X q : MvPolynomial σ F) else X s)

theorem substVar_X_self (p q : σ) : substVar (F := F) p q (X p) = X q := by
  simp [substVar]

theorem substVar_X_of_ne {p q s : σ} (h : s ≠ p) : substVar (F := F) p q (X s) = X s := by
  simp [substVar, h]

/-- **The substitution-divisibility kernel.**  `(Xₚ − X_q)` divides `w − ψ w`, where `ψ`
substitutes `Xₚ ↦ X_q`.  (Each monomial `c·X^d` maps to `c·X^{d'}`, and `X^d − X^{d'}` is a
multiple of `Xₚ − X_q`.) -/
theorem sub_X_dvd_sub_subst (p q : σ) (w : MvPolynomial σ F) :
    (X p - X q) ∣ (w - substVar (F := F) p q w) := by
  set ψ : MvPolynomial σ F →ₐ[F] MvPolynomial σ F := substVar p q with hψ
  induction w using MvPolynomial.induction_on with
  | C a => simp [hψ, substVar]
  | add f g hf hg =>
      rw [map_add]
      have : f + g - (ψ f + ψ g) = (f - ψ f) + (g - ψ g) := by ring
      rw [this]; exact dvd_add hf hg
  | mul_X r s hr =>
      rw [map_mul]
      have hsX : ψ (X s) = (if s = p then (X q : MvPolynomial σ F) else X s) := by
        rw [hψ, substVar, aeval_X]
      rw [hsX]
      have hXs : (X p - X q) ∣ (X s - (if s = p then (X q : MvPolynomial σ F) else X s)) := by
        by_cases h : s = p
        · subst h; simp
        · simp [h]
      have key : r * X s - ψ r * (if s = p then (X q : MvPolynomial σ F) else X s)
          = (r - ψ r) * X s + ψ r * (X s - (if s = p then (X q : MvPolynomial σ F) else X s)) := by
        ring
      rw [key]
      exact dvd_add (Dvd.dvd.mul_right hr _) (Dvd.dvd.mul_left hXs _)

/-- **Lemma 2.5 divisibility corollary.**  If the merge substitution `Xₚ ↦ X_q` kills `w`, then
`(Xₚ − X_q)` divides `w`.  (Apply `sub_X_dvd_sub_subst` and use `ψ w = 0`.) -/
theorem sub_X_dvd_of_subst_eq_zero {p q : σ} {w : MvPolynomial σ F}
    (h : substVar (F := F) p q w = 0) : (X p - X q) ∣ w := by
  have := sub_X_dvd_sub_subst (F := F) p q w
  rwa [h, sub_zero] at this

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.sub_X_dvd_sub_subst
#print axioms ArkLib.GMMDS.sub_X_dvd_of_subst_eq_zero
