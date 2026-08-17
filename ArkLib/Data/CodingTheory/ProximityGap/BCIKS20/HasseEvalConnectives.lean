/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Hasse-derivative evaluation connectives for the App-A.4 Faa-di-Bruno match (issue #9)

The polynomial-level Y-Hasse commutation and the un-shifted coefficient-sum form of
`hasseEvalAtRoot` (the P2-independent bridge the RestrictedFaaDiBrunoMatch assembly re-keys
against). The two confirmed-in-tree facts (evalX_hasseDeriv_Y_coeff, the hasseEvalAtRoot unfold)
are carried as explicit hypotheses to keep the file standalone-checkable against pure Mathlib.
-/


open Polynomial Finset

namespace Issue9Hensel

/-! ## Part 0 — the landed mathlib core (★), re-derived standalone for self-containment.

This is `Polynomial.hasseDeriv_eval_eq_sum` from `ArkLib/ToMathlib/Polynomial/HasseDerivEval.lean`
(already pushed to main, axiom-clean).  Re-proved here verbatim against pure mathlib so this scratch
file env-leans WITHOUT the BCIKS20 dep tree (which is mid-churn).  -/

theorem hasseDeriv_eval_eq_sum {R : Type*} [CommRing R] (k : ℕ) (p : R[X]) (a : R) :
    (hasseDeriv k p).eval a
      = ∑ i ∈ Finset.range (p.natDegree + 1), (i.choose k : R) * p.coeff i * a ^ (i - k) := by
  set D := p.natDegree with hD
  have hbd : (hasseDeriv k p).natDegree < D + 1 :=
    Nat.lt_succ_of_le ((natDegree_hasseDeriv_le p k).trans (Nat.sub_le _ _))
  rw [eval_eq_sum_range' hbd]
  have hL : ∀ n ∈ Finset.range (D + 1),
      (hasseDeriv k p).coeff n * a ^ n
        = ((n + k).choose k : R) * p.coeff (n + k) * a ^ n := by
    intro n _; rw [hasseDeriv_coeff]
  rw [Finset.sum_congr rfl hL]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (D + 1)) (fun i => k ≤ i)]
  have hlow : ∑ i ∈ (Finset.range (D + 1)).filter (fun i => ¬ k ≤ i),
        (i.choose k : R) * p.coeff i * a ^ (i - k) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [Nat.choose_eq_zero_of_lt (not_le.mp hi.2)]; simp
  rw [hlow, add_zero]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (D + 1)) (fun n => n + k ≤ D)]
  have hhi : ∑ n ∈ (Finset.range (D + 1)).filter (fun n => ¬ n + k ≤ D),
        ((n + k).choose k : R) * p.coeff (n + k) * a ^ n = 0 := by
    refine Finset.sum_eq_zero (fun n hn => ?_)
    rw [Finset.mem_filter] at hn
    rw [show p.coeff (n + k) = 0 from
      coeff_eq_zero_of_natDegree_lt (by rw [← hD]; omega)]
    ring
  rw [hhi, add_zero]
  refine Finset.sum_bij' (fun i _ => i - k) (fun n _ => n + k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    dsimp only; omega
  · intro n hn
    dsimp only; omega
  · intro i hi
    rw [Finset.mem_filter] at hi
    have hik : k ≤ i := hi.2
    rw [Nat.sub_add_cancel hik]

/-! ## Part 1 — (B1) the POLYNOMIAL-level Y-Hasse commutation.

The in-tree `evalX_hasseDeriv_Y_coeff` (P2BijectionApply.lean:154) proves the COEFFICIENT identity

    (evalX(C x₀)(Δ_X^{i₁}(Δ_Y^m R))).coeff i = C(i+m,m) • (evalX(C x₀)(Δ_X^{i₁} R)).coeff (i+m).

We carry that exact statement as the hypothesis `hcoeff` and lift it to the POLYNOMIAL equality

    evalX(C x₀)(Δ_X^{i₁}(Δ_Y^m R)) = hasseDeriv m (evalX(C x₀)(Δ_X^{i₁} R))

via `Polynomial.ext` + mathlib `hasseDeriv_coeff` (which gives the SAME C(i+m,m) • coeff(i+m) shape
for the RHS).  This is the polynomial source the match needs; the in-tree coeff lemma alone is
insufficient because the (★) evaluation identity is stated at the polynomial level.

`P` here abstracts `evalX(C x₀)(Δ_X^{i₁} R) : F[X][Y]` (a single-variable polynomial over `F[X]`),
`Pshift` abstracts `evalX(C x₀)(Δ_X^{i₁}(Δ_Y^m R))`. -/

variable {F : Type*} [Field F]

theorem evalX_hasseDerivX_hasseDerivY_eq
    (m : ℕ) (P Pshift : Polynomial (Polynomial F))
    (hcoeff : ∀ i, Pshift.coeff i = (i + m).choose m • P.coeff (i + m)) :
    Pshift = hasseDeriv m P := by
  ext i
  -- LHS: `(i+m).choose m • P.coeff (i+m)` ; RHS (`hasseDeriv_coeff`): `↑((i+m).choose m) * P.coeff
    (i+m)`.
  rw [hcoeff i, hasseDeriv_coeff, nsmul_eq_mul]

/-! ## Part 2 — (B2) `hasseEvalAtRoot` as an ordinary `hasseDeriv` evaluation.

`hasseEvalAtRoot i₁ m = eval₂ lift (T/W) (evalX(C x₀)(Δ_X^{i₁}(Δ_Y^m R)))` (its definition, carried
as `hEval`).  Rewriting the argument by (B1) gives the `eval₂`-of-`hasseDeriv` form.  We state this
generically: `L` = the target field, `lift : R →+* L` the coefficient ring hom, `a : L` the root.

This is a pure `eval₂` rewrite: substitute the (B1) polynomial equality under `eval₂`. -/

variable {R L : Type*} [CommRing R] [CommRing L]

theorem hasseEvalAtRoot_eq_eval₂_hasseDeriv
    (lift : R →+* L) (a : L) (m : ℕ) (P Pshift : R[X])
    (hcoeff : ∀ i, Pshift.coeff i = (i + m).choose m • P.coeff (i + m))
    (val : L) (hEval : val = Polynomial.eval₂ lift a Pshift) :
    val = Polynomial.eval₂ lift a (hasseDeriv m P) := by
  rw [hEval]
  congr 1
  -- (B1) at the abstract `R[X]` level (same proof as Part 1, char-free).
  ext i
  rw [hcoeff i, hasseDeriv_coeff, nsmul_eq_mul]

/-! ## Part 3 — the UN-shifted coefficient-sum form of `hasseEvalAtRoot`, via (B2) ∘ (★).

Composing (B2) with the landed core (★) `hasseDeriv_eval_eq_sum` (specialised through `eval₂` by the
`eval₂ lift a = (map lift _).eval a` bridge, mathlib `eval₂_eq_eval_map`) gives

    hasseEvalAtRoot i₁ m
      = ∑_{i ≤ deg (map lift P)} C(i,m) · lift(P.coeff i) · a^{i−m}.

This is the `B_coeff`-side representative shape (un-shifted, full Y-degree index `i`), which the
match-assembly re-keys against the partition LHS.  Stated abstractly; the BCIKS20 instantiation is
`lift = liftToFunctionField`, `a = T/W = functionFieldT / lift(lc H)`, `P = evalX(C x₀)(Δ_X^{i₁}
  R)`,
`m = Σλ`. -/

theorem hasseEvalAtRoot_eq_unshifted_sum
    (lift : R →+* L) (a : L) (m : ℕ) (P Pshift : R[X])
    (hcoeff : ∀ i, Pshift.coeff i = (i + m).choose m • P.coeff (i + m))
    (val : L) (hEval : val = Polynomial.eval₂ lift a Pshift) :
    val = ∑ i ∈ Finset.range ((P.map lift).natDegree + 1),
            (i.choose m : L) * (P.map lift).coeff i * a ^ (i - m) := by
  rw [hasseEvalAtRoot_eq_eval₂_hasseDeriv lift a m P Pshift hcoeff val hEval]
  -- eval₂ lift a (hasseDeriv m P) = (map lift (hasseDeriv m P)).eval a
  rw [Polynomial.eval₂_eq_eval_map]
  -- map lift (hasseDeriv m P) = hasseDeriv m (map lift P)  (mathlib `hasseDeriv_map`-style;
  -- proven here via coeff since the C(i+m,m) cast commutes with `lift`).
  have hmap : (hasseDeriv m P).map lift = hasseDeriv m (P.map lift) := by
    ext i
    rw [Polynomial.coeff_map, hasseDeriv_coeff, hasseDeriv_coeff, Polynomial.coeff_map,
      map_mul, map_natCast]
  rw [hmap, hasseDeriv_eval_eq_sum]

end Issue9Hensel
