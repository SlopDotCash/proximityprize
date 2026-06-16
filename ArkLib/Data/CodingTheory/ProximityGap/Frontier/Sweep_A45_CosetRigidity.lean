/-
# Char-0 coset rigidity: lacunary ⟹ binomial ⟹ coset (#444, capstone of the char-0 half)

`Sweep_A44` proved a vanishing-sum subset of `μ_{2^μ}` is negation-closed (`T = −T`). This file
closes the char-0 rigidity: if the vanishing product `∏_{t∈T}(X − t)` is a **lacunary trinomial**
`X^a − α·X − c` (the binding shape `e₁ = … = e_{a−2} = 0`), then `α = 0` — the product is the
**binomial** `X^a − c`, whose roots are a `μ_a`-coset. So a lacunary subset is a coset in
characteristic `0`: the dyadic-lacunary count equals the coset count, the complete and correct bound,
with **no char-0 defect**. The single char-0 input is `T = −T`, which fails in characteristic
`p ≡ 1 mod 2^μ` (cyclotomic splits) — the open core.

Mechanism (`p`-free): negation-closure gives `g(−X) = (−1)^{|T|} g(X)`; comparing `X⁰` coefficients
with `c = ±∏ t ≠ 0` forces `(−1)^{|T|} = 1`, then comparing `X¹` coefficients forces `2α = 0`.

Axiom-clean: field + polynomial algebra. No `sorry`.
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace ArkLib.ProximityGap.EvenOddDescent

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `n`-th coefficient of `p(−X)` is `(−1)ⁿ` times the `n`-th coefficient of `p`. -/
theorem coeff_comp_neg_X (p : F[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1) ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial e b =>
    have hrw : (C b * (-X) ^ e : F[X]) = C (b * (-1) ^ e) * X ^ e := by
      rw [show (-X : F[X]) = C (-1) * X by simp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
    rw [monomial_comp, hrw, coeff_C_mul, coeff_X_pow, coeff_monomial]
    by_cases h : n = e
    · subst h; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg h, if_neg (fun he => h he.symm)]; ring

/-- For a negation-closed finite set `T`, `∏_{t∈T}(X − t)` satisfies
`g.comp(−X) = (−1)^{|T|} · g`. -/
theorem prod_X_sub_C_comp_neg (T : Finset F) (hneg : T.image Neg.neg = T) :
    (∏ t ∈ T, (X - C t)).comp (-X) = (-1) ^ T.card * ∏ t ∈ T, (X - C t) := by
  rw [Polynomial.prod_comp]
  have hfac : ∀ t ∈ T, (X - C t).comp (-X) = (-1) * (X + C t) := by
    intro t _; simp only [sub_comp, X_comp, C_comp]; ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const]
  have hre : ∏ t ∈ T, (X + C t) = ∏ s ∈ T, (X - C s) := by
    conv_rhs => rw [← hneg]
    rw [Finset.prod_image (fun a _ b _ h => neg_injective h)]
    exact Finset.prod_congr rfl (fun t _ => by rw [C_neg]; ring)
  rw [hre]

/-- **Char-0 coset rigidity (capstone).** If the vanishing product of a negation-closed set `T`
(`0 ∉ T`, char `≠ 2`) is a lacunary trinomial `X^a − α·X − c` with `a ≥ 2`, then `α = 0`. So a lacunary
subset of `μ_{2^μ}` is, in characteristic 0, the root set of a binomial `X^a − c` — a coset; the
dyadic-lacunary count equals the coset count (no char-0 defect). -/
theorem lacunary_coset_rigidity (T : Finset F) (hneg : T.image Neg.neg = T) (h0 : (0 : F) ∉ T)
    (h2 : (2 : F) ≠ 0) {a : ℕ} (ha : 2 ≤ a) (α c : F)
    (hg : (∏ t ∈ T, (X - C t)) = X ^ a - C α * X - C c) :
    α = 0 := by
  set p : F[X] := X ^ a - C α * X - C c with hp
  -- transport the negation-symmetry to `p`
  have hcomp : p.comp (-X) = (-1) ^ T.card * p := by
    have h := prod_X_sub_C_comp_neg T hneg; rw [hg] at h; rw [hp]; exact h
  -- coefficients of the trinomial `p` at 0 and 1 (using `a ≥ 2`)
  have hp0 : p.coeff 0 = -c := by
    rw [hp, coeff_sub, coeff_sub, coeff_X_pow, if_neg (by omega), coeff_C_mul, coeff_X,
      if_neg (by omega), coeff_C, if_pos rfl]; ring
  have hp1 : p.coeff 1 = -α := by
    rw [hp, coeff_sub, coeff_sub, coeff_X_pow, if_neg (by omega), coeff_C_mul, coeff_X,
      if_pos rfl, coeff_C, if_neg one_ne_zero]; ring
  -- `c ≠ 0` since `−c = p.coeff 0 = ∏_{t∈T}(−t) ≠ 0`
  have hc : c ≠ 0 := by
    have hpc : (∏ t ∈ T, (X - C t)).coeff 0 = ∏ t ∈ T, (-t) := by
      rw [coeff_zero_eq_eval_zero, eval_prod]
      exact Finset.prod_congr rfl (fun t _ => by simp)
    have hprod : (∏ t ∈ T, (-t)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro t ht
      exact neg_ne_zero.mpr (fun h => h0 (h ▸ ht))
    rw [hg, hp0] at hpc  -- -c = ∏ (-t)
    intro hc0; exact hprod (by rw [← hpc, hc0, neg_zero])
  -- read off coefficients of `hcomp`, using the helper for the left side
  have hCpow : ((-1 : F[X]) ^ T.card) = C ((-1 : F) ^ T.card) := by
    rw [← C_1, ← C_neg, ← C_pow]
  -- `(-1)^{card} = 1` from the `X⁰` coefficient of `hcomp` and `c ≠ 0`
  have hone : ((-1 : F) ^ T.card) = 1 := by
    have h := congrArg (fun q => Polynomial.coeff q 0) hcomp
    simp only [coeff_comp_neg_X, hCpow, coeff_C_mul, hp0, pow_zero, one_mul] at h
    have hcne : (-c) ≠ 0 := neg_ne_zero.mpr hc
    have hz : ((-1 : F) ^ T.card - 1) * (-c) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hz with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hcne
  -- `α = 0` from the `X¹` coefficient and `(-1)^{card} = 1`
  have h := congrArg (fun q => Polynomial.coeff q 1) hcomp
  simp only [coeff_comp_neg_X, hCpow, coeff_C_mul, hp1, hone, pow_one, one_mul, mul_neg,
    neg_neg, neg_one_mul] at h
  -- `h : α = -α`
  have h2α : (2 : F) * α = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2α with h' | h'
  · exact absurd h' h2
  · exact h'

end ArkLib.ProximityGap.EvenOddDescent
