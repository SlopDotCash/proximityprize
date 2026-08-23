/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Q1ClaimADyadic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Q1 char-0 sharpening — Claim B: exact degree of the odd part, issue #407

This file packages **Claim B** of the Q1 char-0 sharpening
(`docs/kb/deltastar-407-Q1-inequality-sharpened-2026-06-14.md`), built on **Claim A**
(`Q1ClaimADyadic.lean`: `e_1(S) = ∑_{x∈S} x = 0 ⟺ S = −S` for `2^μ`-th roots of unity).

For a `2k`-subset `S` (`4k` a power of `2`) of the roots of unity, write the monic vanishing
polynomial `σ_S(z) = ∏_{s∈S}(z − s)` in its even/odd split

  `σ_S(z) = G(z²) + z · H(z²)`,

where `G` is the **even part** (`G.coeff j = σ_S.coeff (2j)`) and `H` the **odd part**
(`H.coeff j = σ_S.coeff (2j+1)`).  The split is genuine: `evenPart_oddPart_decomposition`
proves `σ_S = (expand 2 G) + X · (expand 2 H)` exactly (`expand 2 P = P(X²)`).

**Claim B.** The top odd coefficient `H.coeff (k−1)` (the `w^{k−1}` coefficient of `H`) equals
`−e_1(S)`.  Hence `deg H = k − 1` **exactly** iff `e_1(S) ≠ 0`, which by Claim A is iff `S ≠ −S`:

  `coeff_oddPart_top`          : `H.coeff (k−1) = −e_1(S)`,
  `degree_oddPart_eq_iff`      : `deg H = k−1 ⟺ e_1(S) ≠ 0`,
  `degree_oddPart_eq_iff_not_antipodal` : `deg H = k−1 ⟺ S ≠ −S`  (the headline).

## On `degree` vs `natDegree` (honest)

We state the exact-degree result with `Polynomial.degree` (`WithBot ℕ`), the **robust** form:
when `e_1(S) = 0` and `k = 1`, `H = 0` has `degree = ⊥ ≠ ↑0` and is correctly excluded.  The
`natDegree` form would be *false* at this `k = 1, H = 0` boundary (`natDegree 0 = 0 = k−1`); the
load-bearing nonvanishing is the coefficient statement `coeff_oddPart_top_ne_zero_iff`.

## Scope (honest)

This is the **characteristic-0** statement only (the tie to Claim A uses Lam–Leung at the prime 2,
which is char-0).  The structural degree facts (`coeff_oddPart_top`, `degree_oddPart_eq_iff`,
`evenPart_oddPart_decomposition`) are char-free; only the antipodal corollary needs `CharZero`.
The char-`p` simultaneous-rigidity (whether odd power sums vanish mod `p` for antipodal-free `S`
at prize scale) is the open NOVEL-A problem and is **not** addressed.

Axiom-clean.  Issue #407.
-/

open Polynomial Finset

namespace ProximityGap

namespace Q1ClaimB

variable {F : Type*} [Field F] [DecidableEq F]

/-- `σ_S(z) = ∏_{x ∈ S} (z − x)`, the monic vanishing polynomial of `S`. -/
noncomputable def sigma (S : Finset F) : F[X] := ∏ x ∈ S, (X - C x)

/-- The **even part** `G` of a polynomial: `G.coeff j = P.coeff (2*j)`. -/
noncomputable def evenPart (P : F[X]) : F[X] :=
  ∑ j ∈ range (P.natDegree + 1), C (P.coeff (2 * j)) * X ^ j

/-- The **odd part** `H` of a polynomial: `H.coeff j = P.coeff (2*j+1)`. -/
noncomputable def oddPart (P : F[X]) : F[X] :=
  ∑ j ∈ range (P.natDegree + 1), C (P.coeff (2 * j + 1)) * X ^ j

/-- Coefficients of the even part, **total** (holds for all `j`): beyond `natDegree`, both sides
vanish, since `2*j > natDegree ⟹ P.coeff (2*j) = 0`. -/
theorem coeff_evenPart (P : F[X]) (j : ℕ) : (evenPart P).coeff j = P.coeff (2 * j) := by
  classical
  by_cases hj : j ≤ P.natDegree
  · unfold evenPart
    rw [finset_sum_coeff, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  · rw [coeff_eq_zero_of_natDegree_lt (n := 2 * j) (by omega)]
    unfold evenPart
    rw [finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-- Coefficients of the odd part, **total** (holds for all `j`): beyond `natDegree`, both sides
vanish, since `2*j+1 > natDegree ⟹ P.coeff (2*j+1) = 0`. -/
theorem coeff_oddPart (P : F[X]) (j : ℕ) : (oddPart P).coeff j = P.coeff (2 * j + 1) := by
  classical
  by_cases hj : j ≤ P.natDegree
  · unfold oddPart
    rw [finset_sum_coeff, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  · rw [coeff_eq_zero_of_natDegree_lt (n := 2 * j + 1) (by omega)]
    unfold oddPart
    rw [finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-- **The even/odd split is genuine**: `P(z) = G(z²) + z·H(z²)`, i.e.
`P = expand 2 (evenPart P) + X · expand 2 (oddPart P)` (where `expand 2 Q = Q(X²)`).  Char-free. -/
theorem evenPart_oddPart_decomposition (P : F[X]) :
    P = (expand F 2) (evenPart P) + X * (expand F 2) (oddPart P) := by
  ext n
  rw [coeff_add, coeff_expand (by norm_num) (evenPart P) n]
  rcases Nat.even_or_odd n with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- n = 2t even
    subst ht
    rw [if_pos ⟨t, by ring⟩]
    have hdiv : (t + t) / 2 = t := by omega
    rw [hdiv, coeff_evenPart]
    have hxmul : (X * (expand F 2) (oddPart P)).coeff (t + t) = 0 := by
      cases t with
      | zero => simpa using coeff_X_mul_zero _
      | succ s =>
        have : s + 1 + (s + 1) = (s + s + 1) + 1 := by ring
        rw [this, coeff_X_mul, coeff_expand (by norm_num) (oddPart P),
          if_neg (by omega)]
    rw [hxmul, add_zero]
    congr 1; omega
  · -- n = 2t+1 odd
    subst ht
    rw [if_neg (by omega)]
    have h1 : 2 * t + 1 = (2 * t) + 1 := by ring
    rw [h1, coeff_X_mul, coeff_expand (by norm_num) (oddPart P), if_pos ⟨t, by ring⟩,
      zero_add]
    have hdiv : (2 * t) / 2 = t := by omega
    rw [hdiv, coeff_oddPart]

/-- `σ_S` has degree `S.card`. -/
@[simp] theorem natDegree_sigma (S : Finset F) : (sigma S).natDegree = S.card := by
  unfold sigma
  simpa using natDegree_finset_prod_X_sub_C_eq_card S (fun x => x)

/-- The second-from-top coefficient of `σ_S` is `−e_1(S)` (Vieta / `nextCoeff`). -/
theorem coeff_sigma_card_pred (S : Finset F) (hS : 0 < S.card) :
    (sigma S).coeff (S.card - 1) = - ∑ x ∈ S, x := by
  have hnc : nextCoeff (sigma S) = - ∑ x ∈ S, x := by
    unfold sigma
    simpa using prod_X_sub_C_nextCoeff (s := S) (f := fun x => x)
  rwa [nextCoeff_of_natDegree_pos (by simpa using hS), natDegree_sigma] at hnc

/-- The odd part of `σ_S` has degree at most `k − 1` when `S.card = 2*k`. -/
theorem natDegree_oddPart_sigma_le {k : ℕ} {S : Finset F} (hcard : S.card = 2 * k) :
    (oddPart (sigma S)).natDegree ≤ k - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_oddPart]
  apply coeff_eq_zero_of_natDegree_lt
  rw [natDegree_sigma, hcard]
  omega

/-- **Claim B (the coefficient identity).** The top possible odd coefficient `H.coeff (k−1)`
of `σ_S` equals `−e_1(S)`, when `S.card = 2*k` and `k ≥ 1`.  This is the `w^{k-1}` coefficient
of `H` in the even/odd split `σ_S(z) = G(z²) + z·H(z²)`. -/
theorem coeff_oddPart_top {k : ℕ} {S : Finset F} (hcard : S.card = 2 * k) (hk : 1 ≤ k) :
    (oddPart (sigma S)).coeff (k - 1) = - ∑ x ∈ S, x := by
  rw [coeff_oddPart]
  have h2 : 2 * (k - 1) + 1 = S.card - 1 := by rw [hcard]; omega
  rw [h2, coeff_sigma_card_pred S (by omega)]

/-- **Claim B (clean coefficient iff).** The top odd coefficient is nonzero iff `e_1(S) ≠ 0`. -/
theorem coeff_oddPart_top_ne_zero_iff {k : ℕ} {S : Finset F}
    (hcard : S.card = 2 * k) (hk : 1 ≤ k) :
    (oddPart (sigma S)).coeff (k - 1) ≠ 0 ↔ ∑ x ∈ S, x ≠ 0 := by
  rw [coeff_oddPart_top hcard hk, neg_ne_zero]

/-- **Claim B (exact degree, robust `degree` form).** For `S.card = 2*k` with `k ≥ 1`, the odd
part `H` of `σ_S = G(z²) + z·H(z²)` has `degree` **exactly** `k − 1` iff `e_1(S) = ∑_{x∈S} x ≠ 0`.

The `degree` (`WithBot ℕ`) form is the robust statement: when `e_1 = 0` and `k = 1`, `H = 0` has
`degree = ⊥ ≠ ↑0`, correctly distinguished — unlike `natDegree`, where `natDegree 0 = 0`. -/
theorem degree_oddPart_eq_iff {k : ℕ} {S : Finset F} (hcard : S.card = 2 * k) (hk : 1 ≤ k) :
    (oddPart (sigma S)).degree = (k - 1 : ℕ) ↔ ∑ x ∈ S, x ≠ 0 := by
  constructor
  · intro hdeg
    have hne : oddPart (sigma S) ≠ 0 := by
      intro h0; rw [h0, degree_zero] at hdeg; exact (WithBot.bot_ne_coe).elim hdeg
    have hnd : (oddPart (sigma S)).natDegree = k - 1 := natDegree_eq_of_degree_eq_some hdeg
    have hcoeff : (oddPart (sigma S)).coeff (k - 1) ≠ 0 := by
      rw [← hnd, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hne
    exact (coeff_oddPart_top_ne_zero_iff hcard hk).mp hcoeff
  · intro hsum
    have hcoeff : (oddPart (sigma S)).coeff (k - 1) ≠ 0 :=
      (coeff_oddPart_top_ne_zero_iff hcard hk).mpr hsum
    refine le_antisymm ?_ (le_degree_of_ne_zero hcoeff)
    calc (oddPart (sigma S)).degree
        ≤ ((oddPart (sigma S)).natDegree : WithBot ℕ) := degree_le_natDegree
      _ ≤ (k - 1 : ℕ) := by exact_mod_cast natDegree_oddPart_sigma_le hcard

/-- **Claim B, the iff tied to Claim A (the headline).** For a `2k`-subset `S` of the
`2^(m+1)`-th roots of unity in characteristic zero, the odd part `H` of `σ_S = G(z²) + z·H(z²)`
has `degree` exactly `k − 1` **iff** `S` is *not* antipodal-symmetric (`S.image (−·) ≠ S`).

Combining `coeff_oddPart_top` (deg `H = k−1 ⟺ e_1(S) ≠ 0`) with Claim A
(`e_1(S) = 0 ⟺ S = −S`): the odd part attains its maximal degree exactly when `S ≠ −S`. -/
theorem degree_oddPart_eq_iff_not_antipodal [CharZero F] {m k : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {S : Finset F} (hroots : ∀ x ∈ S, x ^ (2 ^ (m + 1)) = 1)
    (hcard : S.card = 2 * k) (hk : 1 ≤ k) :
    (oddPart (sigma S)).degree = (k - 1 : ℕ) ↔ S.image (fun x => -x) ≠ S := by
  rw [degree_oddPart_eq_iff hcard hk]
  exact (not_congr (Q1ClaimA.sum_eq_zero_iff_image_neg_eq hζ hroots))

end Q1ClaimB

end ProximityGap

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ProximityGap.Q1ClaimB.evenPart_oddPart_decomposition
#print axioms ProximityGap.Q1ClaimB.coeff_oddPart_top
#print axioms ProximityGap.Q1ClaimB.degree_oddPart_eq_iff
#print axioms ProximityGap.Q1ClaimB.degree_oddPart_eq_iff_not_antipodal
