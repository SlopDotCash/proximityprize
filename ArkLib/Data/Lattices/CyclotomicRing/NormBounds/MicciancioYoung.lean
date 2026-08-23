/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic

/-!
# The Micciancio/Young Product Norm-Growth Bound

The Young/Micciancio inequality `‖(c·d)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the power-of-two
negacyclic convolution (`φ = X^{2^α} + 1`, `powTwoCyclotomic α`) with centered
representatives: scaling an already-`c`-scaled vector by a further ring element `d` of
bounded centered `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`.

The statement is pinned to `powTwoCyclotomic α`: the per-entry product bound
`‖d·w‖₂ ≤ ‖d‖₁·‖w‖₂` rests on multiplication-by-`X` being an `ℓ₂`-isometry on the
coefficient vector, which holds for the cyclic/negacyclic rings `X^n ∓ 1` of [Mic07] but
*fails* for a general cyclotomic `Φ_m` (e.g. in `ℤ[X]/(X²+X+1)`, `‖X·X‖₂ = √2 > ‖X‖₁·‖X‖₂`).
Phrasing this for an arbitrary `Φ` would therefore be unsound.

This is one of the two unproven lemmas for the Greyhound [NS24] / Hachi [NOZ26]
weak-binding argument. The paper proof is in [Mic07, Lemma 2]: discrete Cauchy–Schwarz over
the negacyclic convolution, together with minimality of the centered representative, gives the
product norm inequality `‖fg‖ ≤ ‖f‖₁·‖g‖`.

## References

* [Micciancio, D., *Generalized Compact Knapsacks, Cyclic Lattices, and Efficient One-Way
    Functions*][Mic07]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

open Polynomial

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

/-- The power-of-two ("Hachi") cyclotomic modulus `X^{2^α}+1` over `ZMod q`. -/
local notation "Φ" => (powTwoCyclotomic (R := ZMod q) α)

/-! ## Negacyclic convolution coefficient machinery

The proof of the Micciancio/Young product bound reduces, via the `toPoly` bridge into
`Polynomial (ZMod q)`, to a discrete Cauchy–Schwarz over the negacyclic convolution
`X^{2^α} ≡ -1`. We build the coefficient identity for reduction modulo a monic binomial
`X^n + 1`, lift it to a bound over the *centered* (`valMinAbs`) integer representatives,
and then run the [Mic07, Lemma 2] double-counting argument. -/

omit [NeZero q] in
/-- The Mathlib polynomial underlying the power-of-two modulus is `X^{2^α} + 1`. -/
theorem powTwo_toPoly :
    (Φ).φ.toPoly = (Polynomial.X : (ZMod q)[X]) ^ (2 ^ α) + 1 := by
  change (CompPoly.CPolynomial.X ^ (2 ^ α) + 1 : CompPoly.CPolynomial (ZMod q)).toPoly = _
  rw [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.toPoly_X, CompPoly.CPolynomial.toPoly_one]

/-- The Mathlib degree of the power-of-two modulus is `2^α`. -/
theorem powTwo_toPoly_natDegree : (Φ).φ.toPoly.natDegree = 2 ^ α := by
  rw [powTwo_toPoly, ← Polynomial.C_1, natDegree_X_pow_add_C]

/-- The `CPolynomial` degree of the modulus is `2^α`; this is the index range of the
centered norms. -/
theorem powTwo_natDegree : (Φ).φ.natDegree = 2 ^ α := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, powTwo_toPoly_natDegree]

/-- A reduced representative has all coefficients beyond `2^α` equal to zero. -/
theorem coeff_toPoly_eq_zero_of_le {a : Rq Φ} {i : ℕ} (hi : 2 ^ α ≤ i) :
    a.1.toPoly.coeff i = 0 := by
  apply Polynomial.coeff_eq_zero_of_degree_lt
  refine lt_of_lt_of_le (CyclotomicModulus.degree_toPoly_lt_of_reduced _ a.2) ?_
  rw [powTwo_toPoly, ← Polynomial.C_1, degree_X_pow_add_C (by positivity)]
  exact_mod_cast hi

/-- A reduced representative has Mathlib degree strictly below `2^α`. -/
theorem natDegree_toPoly_lt (a : Rq Φ) : a.1.toPoly.natDegree < 2 ^ α := by
  rcases eq_or_ne a.1.toPoly 0 with h | h
  · rw [h, Polynomial.natDegree_zero]; positivity
  · rw [Polynomial.natDegree_lt_iff_degree_lt h]
    refine lt_of_lt_of_le (CyclotomicModulus.degree_toPoly_lt_of_reduced _ a.2) ?_
    rw [powTwo_toPoly, ← Polynomial.C_1, degree_X_pow_add_C (by positivity)]

/-- The integer-cast of a centered representative recovers the coefficient in `ZMod q`. -/
theorem intCast_valMinAbs_coeff (a : Rq Φ) (i : ℕ) :
    (((a.1.coeff i).valMinAbs : ℤ) : ZMod q) = a.1.toPoly.coeff i := by
  rw [ZMod.coe_valMinAbs, CompPoly.CPolynomial.coeff_toPoly]

/-- Coefficient identity for reduction modulo the monic binomial `X^n + 1` over any
commutative ring: for a polynomial `f` of degree `< 2n` and `k < n`, the negacyclic
wraparound `X^{n+k} ≡ -X^k` collapses the two contributing degrees into a signed
difference `(f %ₘ (X^n+1)).coeff k = f.coeff k − f.coeff (n+k)`. -/
theorem coeff_modByMonic_X_pow_add_one {S : Type*} [CommRing S] [Nontrivial S] {n : ℕ}
    (hn : 0 < n) (f : S[X]) (hf : f.natDegree < 2 * n) {k : ℕ} (hk : k < n) :
    (f %ₘ ((Polynomial.X : S[X]) ^ n + 1)).coeff k = f.coeff k - f.coeff (n + k) := by
  set g : S[X] := (Polynomial.X : S[X]) ^ n + 1 with hg
  have hmon : g.Monic := by rw [hg, ← Polynomial.C_1]; exact monic_X_pow_add_C 1 hn.ne'
  have hgnd : g.natDegree = n := by rw [hg, ← Polynomial.C_1, natDegree_X_pow_add_C]
  set Q : S[X] := f /ₘ g with hQ
  -- The quotient has degree `< n` since `deg f < 2n` and `deg g = n`.
  have hQnd : Q.natDegree < n := by
    have hnd : Q.natDegree = f.natDegree - g.natDegree := Polynomial.natDegree_divByMonic f hmon
    rw [hnd, hgnd]; omega
  -- `f = g * Q + (f %ₘ g)`.
  have hfeq : f = g * Q + f %ₘ g := by
    have := Polynomial.modByMonic_add_div f g; rw [hQ]; linear_combination -this
  -- Expand `g * Q = X^n * Q + Q`.
  have hgQ : g * Q = (Polynomial.X : S[X]) ^ n * Q + Q := by rw [hg]; ring
  -- `(X^n * Q).coeff` behaviour at the two relevant indices.
  have hk1 : ((Polynomial.X : S[X]) ^ n * Q).coeff k = 0 := by
    rw [Polynomial.coeff_X_pow_mul', if_neg (by omega)]
  have hk2 : ((Polynomial.X : S[X]) ^ n * Q).coeff (n + k) = Q.coeff k := by
    rw [Polynomial.coeff_X_pow_mul', if_pos (by omega)]; congr 1; omega
  have hQk2 : Q.coeff (n + k) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hrem : (f %ₘ g).coeff (n + k) = 0 := by
    apply Polynomial.coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le (Polynomial.degree_modByMonic_lt f hmon) ?_
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hgnd]
    exact_mod_cast Nat.le_add_right n k
  -- Read off `f.coeff k` and `f.coeff (n+k)` from `f = g*Q + (f %ₘ g)`.
  have hfk : f.coeff (n + k) = Q.coeff k := by
    conv_lhs => rw [hfeq]
    rw [Polynomial.coeff_add, hgQ, Polynomial.coeff_add, hk2, hQk2, hrem, add_zero, add_zero]
  have hfk0 : f.coeff k = Q.coeff k + (f %ₘ g).coeff k := by
    conv_lhs => rw [hfeq]
    rw [Polynomial.coeff_add, hgQ, Polynomial.coeff_add, hk1, zero_add]
  rw [hfk, hfk0]; ring

/-- The negacyclic index permutation `i ↦ (n + k − i) mod n` on `range n`. For fixed `k < n`
it is an involution, hence a bijection of `range (2^α)`; absolute values are preserved under it,
which is the [Mic07] double-counting that turns the per-coefficient Cauchy–Schwarz into the
global product bound. -/
def negIdx (n k i : ℕ) : ℕ := (n + k - i) % n

omit [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- For `k < n` and `i < n`, the negacyclic index lands in `range n`. -/
theorem negIdx_lt {n k i : ℕ} (hn : 0 < n) : negIdx n k i < n := Nat.mod_lt _ hn

/-- The negacyclic index is `k − i` when `i ≤ k`. -/
theorem negIdx_of_le {n k i : ℕ} (hk : k < n) (hik : i ≤ k) : negIdx n k i = k - i := by
  unfold negIdx
  have h : n + k - i = n + (k - i) := by omega
  rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- The negacyclic index is `n + k − i` when `k < i < n`. -/
theorem negIdx_of_gt {n k i : ℕ} (hi : i < n) (hik : k < i) : negIdx n k i = n + k - i := by
  exact Nat.mod_eq_of_lt (by omega)

/-- The negacyclic index map is an involution on `range n` (for fixed `k < n`). -/
theorem negIdx_negIdx {n k i : ℕ} (hk : k < n) (hi : i < n) :
    negIdx n k (negIdx n k i) = i := by
  rcases le_or_gt i k with hik | hik
  · rw [negIdx_of_le hk hik, negIdx_of_le hk (by omega)]; omega
  · rw [negIdx_of_gt hi hik, negIdx_of_gt (by omega) (by omega)]; omega

/-- Summing over `range n` is invariant under the negacyclic index permutation. -/
theorem sum_negIdx_eq {β : Type*} [AddCommMonoid β] {n k : ℕ} (hk : k < n) (F : ℕ → β) :
    ∑ i ∈ Finset.range n, F (negIdx n k i) = ∑ i ∈ Finset.range n, F i := by
  apply Finset.sum_nbij' (negIdx n k) (negIdx n k)
  · intro i hi; exact Finset.mem_range.mpr (negIdx_lt (by omega))
  · intro i hi; exact Finset.mem_range.mpr (negIdx_lt (by omega))
  · intro i hi; exact negIdx_negIdx hk (Finset.mem_range.mp hi)
  · intro i hi; exact negIdx_negIdx hk (Finset.mem_range.mp hi)
  · intro i hi; rfl

/-- Summing over `range n` in the *index argument* `k` of the negacyclic map is also
permutation-invariant: `k ↦ (n + k − i) mod n` is the rotation by `n − i`, a bijection of
`range n`, with inverse `k ↦ (k + i) mod n`. This is the second leg of the [Mic07]
double-counting. -/
theorem sum_negIdx_eq_k {β : Type*} [AddCommMonoid β] {n i : ℕ} (hi : i < n) (F : ℕ → β) :
    ∑ k ∈ Finset.range n, F (negIdx n k i) = ∑ k ∈ Finset.range n, F k := by
  have hn : 0 < n := by omega
  apply Finset.sum_nbij' (fun k => negIdx n k i) (fun k => (k + i) % n)
  · intro k _; exact Finset.mem_range.mpr (negIdx_lt hn)
  · intro k _; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    change ((n + k - i) % n + i) % n = k
    rw [Nat.add_mod ((n + k - i) % n) i n, Nat.mod_mod, ← Nat.add_mod]
    rw [show n + k - i + i = n + k from by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hk']
  · intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    change negIdx n ((k + i) % n) i = k
    unfold negIdx
    set m := (k + i) % n with hm
    have hmlt : m < n := Nat.mod_lt _ hn
    have hmod : (n + m - i) % n = k := by
      have hcong : (n + m - i) ≡ k [MOD n] := by
        have hcancel : (n + m - i) + i ≡ k + i [MOD n] := by
          rw [show n + m - i + i = n + m from by omega]
          calc n + m ≡ 0 + (k + i) [MOD n] := by
                refine Nat.ModEq.add ?_ ?_
                · exact (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
                · rw [hm]; exact (Nat.mod_modEq _ _)
            _ = k + i := by rw [zero_add]
        exact Nat.ModEq.add_right_cancel' i hcancel
      calc (n + m - i) % n = k % n := hcong
        _ = k := Nat.mod_eq_of_lt hk'
    exact hmod
  · intro k _; rfl

/-- **Per-coefficient Mic07 bound.** The centered absolute value of the `k`-th product
coefficient is dominated by the negacyclic convolution of the centered absolute values:
`|（d·w)_k| ≤ Σ_{i<2^α} |d_i|·|w_{σ(k,i)}|`, where `σ` is the negacyclic index map. -/
theorem mul_coeff_valMinAbs_le (d w : Rq Φ) {k : ℕ} (hk : k < 2 ^ α) :
    (((d * w).1.coeff k).valMinAbs.natAbs : ℤ) ≤
      ∑ i ∈ Finset.range (2 ^ α),
        ((d.1.coeff i).valMinAbs.natAbs : ℤ) *
          ((w.1.coeff (negIdx (2 ^ α) k i)).valMinAbs.natAbs : ℤ) := by
  set n := 2 ^ α with hn
  have hnpos : 0 < n := by rw [hn]; positivity
  -- Integer centered representatives.
  set Dz : ℕ → ℤ := fun i => (d.1.coeff i).valMinAbs with hDz
  set Wz : ℕ → ℤ := fun j => (w.1.coeff j).valMinAbs with hWz
  -- The signed negacyclic convolution at index `k`, as an integer.
  set Mk : ℤ := ∑ i ∈ Finset.range n,
      (if i ≤ k then Dz i * Wz (k - i) else - (Dz i * Wz (n + k - i))) with hMk
  -- `Mk` is congruent to the product coefficient in `ZMod q`.
  have hprod : ((d * w).1.coeff k : ZMod q)
      = (d.1.toPoly * w.1.toPoly).coeff k - (d.1.toPoly * w.1.toPoly).coeff (n + k) := by
    rw [CompPoly.CPolynomial.coeff_toPoly]
    have hval : (d * w).1.toPoly = (d.1.toPoly * w.1.toPoly) %ₘ ((Polynomial.X) ^ n + 1) := by
      change (CyclotomicModulus.reduce (powTwoCyclotomic α) (d.1 * w.1)).toPoly = _
      rw [reduce_toPoly, CompPoly.CPolynomial.toPoly_mul, powTwo_toPoly]
    rw [hval, coeff_modByMonic_X_pow_add_one hnpos _ ?_ hk]
    · refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
      have h1 := natDegree_toPoly_lt (α := α) d
      have h2 := natDegree_toPoly_lt (α := α) w
      omega
  -- Cast `Mk` to `ZMod q` and match it with the two product-coefficient antidiagonals.
  have hMkcast : (Mk : ZMod q) = (d * w).1.coeff k := by
    rw [hprod, hMk]
    push_cast
    rw [Finset.sum_ite, Finset.sum_neg_distrib]
    -- Cast each summand to a Mathlib coefficient.
    have hcastDz : ∀ i, (Dz i : ZMod q) = d.1.toPoly.coeff i := fun i => by
      rw [hDz]; exact intCast_valMinAbs_coeff (α := α) d i
    have hcastWz : ∀ j, (Wz j : ZMod q) = w.1.toPoly.coeff j := fun j => by
      rw [hWz]; exact intCast_valMinAbs_coeff (α := α) w j
    -- The `i ≤ k` part matches the antidiagonal of `k`.
    have hposSum : ∑ i ∈ Finset.filter (fun i => i ≤ k) (Finset.range n),
          ((Dz i : ZMod q) * (Wz (k - i) : ZMod q))
        = (d.1.toPoly * w.1.toPoly).coeff k := by
      rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => d.1.toPoly.coeff i * w.1.toPoly.coeff j) k]
      have hfilter : Finset.filter (fun i => i ≤ k) (Finset.range n) = Finset.range (k + 1) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hfilter]
      exact Finset.sum_congr rfl (fun i _ => by rw [hcastDz, hcastWz])
    -- The `i > k` part matches the antidiagonal of `n + k`.
    have hnegSum : ∑ i ∈ Finset.filter (fun i => ¬ i ≤ k) (Finset.range n),
          ((Dz i : ZMod q) * (Wz (n + k - i) : ZMod q))
        = (d.1.toPoly * w.1.toPoly).coeff (n + k) := by
      rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => d.1.toPoly.coeff i * w.1.toPoly.coeff j) (n + k)]
      have hsub : Finset.filter (fun i => ¬ i ≤ k) (Finset.range n) ⊆ Finset.range (n + k + 1) := by
        intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
      rw [show (∑ i ∈ Finset.filter (fun i => ¬ i ≤ k) (Finset.range n),
          ((Dz i : ZMod q) * (Wz (n + k - i) : ZMod q)))
          = ∑ i ∈ Finset.filter (fun i => ¬ i ≤ k) (Finset.range n),
            d.1.toPoly.coeff i * w.1.toPoly.coeff (n + k - i) from
        Finset.sum_congr rfl (fun i _ => by rw [hcastDz, hcastWz])]
      refine Finset.sum_subset hsub (fun i hi hni => ?_)
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not] at hni
      rcases le_or_gt i k with h | h
      · rw [coeff_toPoly_eq_zero_of_le (α := α) (a := w) (i := n + k - i) (by omega), mul_zero]
      · rw [coeff_toPoly_eq_zero_of_le (α := α) (a := d) (i := i)
          (le_of_not_gt (fun hcon => absurd (hni hcon) (by omega))), zero_mul]
    rw [hposSum, hnegSum]
    ring
  -- Minimality of the centered representative.
  have hmin : ((d * w).1.coeff k).valMinAbs.natAbs ≤ Mk.natAbs :=
    valMinAbs_natAbs_le Mk hMkcast
  -- Triangle inequality on `Mk`, then rewrite via the negacyclic index.
  calc (((d * w).1.coeff k).valMinAbs.natAbs : ℤ)
      ≤ (Mk.natAbs : ℤ) := by exact_mod_cast hmin
    _ = |Mk| := (Int.abs_eq_natAbs Mk).symm
    _ ≤ ∑ i ∈ Finset.range n,
          |(if i ≤ k then Dz i * Wz (k - i) else - (Dz i * Wz (n + k - i)))| := by
        rw [hMk]; exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n, |Dz i| * |Wz (negIdx n k i)| := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' : i < n := Finset.mem_range.mp hi
        rcases le_or_gt i k with h | h
        · rw [if_pos h, abs_mul, negIdx_of_le hk h]
        · rw [if_neg (by omega), abs_neg, abs_mul, negIdx_of_gt hi' h]
    _ = ∑ i ∈ Finset.range n,
          ((d.1.coeff i).valMinAbs.natAbs : ℤ) *
            ((w.1.coeff (negIdx n k i)).valMinAbs.natAbs : ℤ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hDz, hWz, Int.abs_eq_natAbs, Int.abs_eq_natAbs]

/-- **Per-element Mic07 product norm bound.** The squared `ℓ₂` norm of a ring product is
bounded by `‖d‖₁²·‖w‖₂²`: the discrete Cauchy–Schwarz over the negacyclic convolution,
double-counted with the [Mic07] permutation `Σ_k |w_{σ(k,i)}|² = ‖w‖₂²`. -/
theorem Rq.l2NormSq_mul_le (d w : Rq Φ) :
    Rq.l2NormSq Φ (d * w) ≤ (Rq.l1Norm Φ d) ^ 2 * Rq.l2NormSq Φ w := by
  -- Abbreviations for the centered absolute values, lifted to `ℤ`.
  set n := 2 ^ α with hn
  set a : ℕ → ℤ := fun i => ((d.1.coeff i).valMinAbs.natAbs : ℤ) with ha
  set b : ℕ → ℤ := fun j => ((w.1.coeff j).valMinAbs.natAbs : ℤ) with hb
  -- It suffices to prove the inequality over `ℤ`.
  rw [← @Nat.cast_le ℤ]
  push_cast
  -- Rewrite both norms as `ℤ`-sums over `range n`.
  have hl2 : ((Rq.l2NormSq Φ (d * w) : ℤ))
      = ∑ k ∈ Finset.range n, (((d * w).1.coeff k).valMinAbs.natAbs : ℤ) ^ 2 := by
    rw [Rq.l2NormSq, powTwo_natDegree (α := α), ← hn]; push_cast; rfl
  have hl1 : ((Rq.l1Norm Φ d : ℤ)) = ∑ i ∈ Finset.range n, a i := by
    rw [Rq.l1Norm, powTwo_natDegree (α := α), ← hn, ha]; push_cast; rfl
  have hl2w : ((Rq.l2NormSq Φ w : ℤ)) = ∑ j ∈ Finset.range n, b j ^ 2 := by
    rw [Rq.l2NormSq, powTwo_natDegree (α := α), ← hn, hb]; push_cast; rfl
  rw [hl2, hl1, hl2w]
  -- Per-coefficient: square the Mic07 bound (both sides nonnegative).
  have hsq : ∀ k ∈ Finset.range n,
      (((d * w).1.coeff k).valMinAbs.natAbs : ℤ) ^ 2
        ≤ (∑ i ∈ Finset.range n, a i * b (negIdx n k i)) ^ 2 := by
    intro k hk
    have hk' : k < 2 ^ α := by simpa [hn] using Finset.mem_range.mp hk
    have hbound := mul_coeff_valMinAbs_le (α := α) d w hk'
    have hbound' : (((d * w).1.coeff k).valMinAbs.natAbs : ℤ)
        ≤ ∑ i ∈ Finset.range n, a i * b (negIdx n k i) := by
      rw [ha, hb]; exact hbound
    have hnonneg : (0 : ℤ) ≤ (((d * w).1.coeff k).valMinAbs.natAbs : ℤ) := by positivity
    exact pow_le_pow_left₀ hnonneg hbound' 2
  -- Cauchy–Schwarz (weighted form) per coefficient.
  have hcs : ∀ k ∈ Finset.range n,
      (∑ i ∈ Finset.range n, a i * b (negIdx n k i)) ^ 2
        ≤ (∑ i ∈ Finset.range n, a i)
            * ∑ i ∈ Finset.range n, a i * b (negIdx n k i) ^ 2 := by
    intro k _
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.range n)
      (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_)
    · positivity
    · have : (0 : ℤ) ≤ a i := by rw [ha]; positivity
      positivity
    · rw [mul_pow]; ring
  -- Chain: `Σ c² ≤ Σ (Σaᵢbσ)² ≤ Σ (Σaⱼ)(Σaᵢbσ²) = (Σaⱼ)·Σ_k Σ_i aᵢbσ²`.
  calc ∑ k ∈ Finset.range n, (((d * w).1.coeff k).valMinAbs.natAbs : ℤ) ^ 2
      ≤ ∑ k ∈ Finset.range n, (∑ i ∈ Finset.range n, a i * b (negIdx n k i)) ^ 2 :=
        Finset.sum_le_sum hsq
    _ ≤ ∑ k ∈ Finset.range n,
          (∑ i ∈ Finset.range n, a i)
            * ∑ i ∈ Finset.range n, a i * b (negIdx n k i) ^ 2 :=
        Finset.sum_le_sum hcs
    _ = (∑ i ∈ Finset.range n, a i)
          * ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range n, a i * b (negIdx n k i) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (∑ i ∈ Finset.range n, a i)
          * ∑ i ∈ Finset.range n, a i * ∑ k ∈ Finset.range n,
              b (negIdx n k i) ^ 2 := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
    _ = (∑ i ∈ Finset.range n, a i)
          * ∑ i ∈ Finset.range n, a i * ∑ k ∈ Finset.range n, b k ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl (fun i hi => ?_)
        congr 1
        exact sum_negIdx_eq_k (Finset.mem_range.mp hi) (fun j => b j ^ 2)
    _ = (∑ i ∈ Finset.range n, a i) ^ 2 * ∑ k ∈ Finset.range n, b k ^ 2 := by
        rw [← Finset.sum_mul, sq]; ring

/-- **Micciancio/Young product bound.** Over the power-of-two cyclotomic modulus
`powTwoCyclotomic α` (`φ = X^{2^α}+1`), scaling an already-`c`-scaled vector by a further
ring element `d` of bounded centered `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`
(the honest Young/Micciancio inequality `‖(c·d)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the negacyclic
convolution with centered representatives, proved by discrete Cauchy–Schwarz in
`Rq.l2NormSq_mul_le`). -/
theorem scalarVecMul_mul_l2NormSq_le {cols : ℕ} (c d : Rq Φ) (v : PolyVec (Rq Φ) cols)
    {κ βSq : ℕ} (hd : Rq.l1Norm Φ d ≤ κ)
    (hv : vecL2NormSq Φ (scalarVecMul c v) ≤ βSq) :
    vecL2NormSq Φ (scalarVecMul (c * d) v) ≤ scalarVecMulMulL2NormSqBound κ βSq := by
  -- Per-entry: `(c·d)·vᵢ = d·(c·vᵢ)`, so `‖(c·d)·vᵢ‖₂² ≤ ‖d‖₁²·‖c·vᵢ‖₂² ≤ κ²·‖c·vᵢ‖₂²`.
  have hentry : ∀ i : Fin cols,
      Rq.l2NormSq Φ (scalarVecMul (c * d) v i) ≤ κ ^ 2 * Rq.l2NormSq Φ (scalarVecMul c v i) := by
    intro i
    simp only [scalarVecMul_apply]
    have hcomm : (c * d) * v i = d * (c * v i) := by ring
    rw [hcomm]
    calc Rq.l2NormSq Φ (d * (c * v i))
        ≤ (Rq.l1Norm Φ d) ^ 2 * Rq.l2NormSq Φ (c * v i) := Rq.l2NormSq_mul_le (α := α) d _
      _ ≤ κ ^ 2 * Rq.l2NormSq Φ (c * v i) := by
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hd 2)
  -- Sum the per-entry bounds.
  calc vecL2NormSq Φ (scalarVecMul (c * d) v)
      = ∑ i : Fin cols, Rq.l2NormSq Φ (scalarVecMul (c * d) v i) := rfl
    _ ≤ ∑ i : Fin cols, κ ^ 2 * Rq.l2NormSq Φ (scalarVecMul c v i) :=
        Finset.sum_le_sum (fun i _ => hentry i)
    _ = κ ^ 2 * vecL2NormSq Φ (scalarVecMul c v) := by
        rw [vecL2NormSq, Finset.mul_sum]
    _ ≤ κ ^ 2 * βSq := Nat.mul_le_mul_left _ hv
    _ = scalarVecMulMulL2NormSqBound κ βSq := rfl

end ArkLib.Lattices.CyclotomicModulus
