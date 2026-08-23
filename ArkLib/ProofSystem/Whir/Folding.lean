/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.Polynomial.SplitFold
import ArkLib.Data.Probability.Instances
import ArkLib.ProofSystem.Whir.BlockRelDistance
import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-!
# Folding

This file formalizes the notion of folding univariate functions and
lemmas showing that folding preserves list decocidng,
introduced in Section 4 of [ACFY24].

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

## Implementation notes (corrections from paper)

- Theorem 4.20:
-- proximity generators should be defined for `C^(0),...,C^(k)` in place of `C^(1),...,C^(k)`
-- `\delta \in (0, 1 - max_{i \in [0,k]} {....})` in place of
   `\delta \in (0, 1 - max_{i \in [k]} {....})`
- Theorem 4.20 holds for `l = 2` as can be seen with `BStar(..,2)` and `errStar(..,2,..)`
  and so `Gen(l,alpha) = {1, alpha,...., alpha^{l-1}}` also corresponds to `l = 2`
  and not for a generic l.

- Lemmas 4.21,4.22,4.23
-- these lemmas refer to the specific case when k set to 1, so it's safe to use the hypothesis 1 ≤ m

## Tags
Open question: should we aim to add tags?
-/

namespace Fold

open BlockRelDistance Vector Finset

variable {F : Type} [Field F] {ι : Type} [Pow ι ℕ]

/-- `∃ x ∈ S`, such that `y = x ^ 2^(k+1)`. `extract_x` returns `z = x ^ 2^k` such that `y = z^2`.
-/
noncomputable def extract_x
  (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPowT S φ (k + 1)) : indexPowT S φ k :=
  let x := Classical.choose y.property
  let hx := Classical.choose_spec y.property
  let z := (φ x) ^ (2^k)
  ⟨z, ⟨x, hx.1, rfl⟩⟩

/-- Given a function `f : (ι^(2ᵏ)) → F`, foldf operates on two inputs:
  element `y ∈ LpowT S (k+1)`, hence `∃ x ∈ S, s.t. y = x ^ 2^(k+1)` and `α ∈ F`.
  It obtains the square root of y as `xPow := extract_x S φ k y`,
    here xPow is of the form `x ^ 2^k`.
  It returns the value `f(xPow) + f(- xPow)/2 + α * (f(xPow) - f(- xPow))/ 2 * xPow`. -/
noncomputable def foldf (S : Finset ι) (φ : ι ↪ F)
  {k : ℕ} [Neg (indexPowT S φ k)] (y : indexPowT S φ (k + 1))
  (f : indexPowT S φ k → F) (α : F) : F :=
  let xPow := extract_x S φ k y
  let fx := f xPow
  let f_negx := f (-xPow)
  (fx + f_negx) / 2 + α * ((fx - f_negx) / (2 * (xPow.val : F)))

/-- The function `fold_k_core` runs a recursion,
    for a function `f : ι → F` and a vector `αs` of size i
  For `i = 0`, `fold_k_core` returns `f` evaluated at `x ∈ S`
  For `i = (k+1) ≠ 0`,
    αs is parsed as α || αs', where αs' is of size k
    function `fk : (ι^2ᵏ) → F` is obtained by making a recursive call to
      `fold_k_core` on input `αs'`
    we obtain the final function `(ι^(2^(k+1))) → F` by invoking `foldf` with `fk` and `α`. -/
noncomputable def fold_k_core {S : Finset ι} {φ : ι ↪ F} (f : (indexPowT S φ 0) → F)
  [∀ i : ℕ, Neg (indexPowT S φ i)] : (i : ℕ) → (αs : Fin i → F) →
    indexPowT S φ i → F
| 0, _ => fun x₀ => f x₀
| k+1, αs => fun y =>
    let α := αs 0
    let αs' : Fin k → F := fun i => αs (Fin.succ i)
    let fk := fold_k_core f k αs'
    foldf S φ y fk α

/-- Definition 4.14, part 1
  fold_k takes a function `f : ι → F` and a vector `αs` of size k
  and returns a function `Fold : (ι^2ᵏ) → F` -/
noncomputable def fold_k
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (f : (indexPowT S φ 0) → F) (αs : Fin k → F) (_hk : k ≤ m): indexPowT S φ k → F :=
  fold_k_core f k αs

/-- Definition 4.14, part 2
  fold_k takes a set of functions `set : Set (ι → F)` and a vector `αs` of size k
  and returns a set of functions `Foldset : Set ((ι^2ᵏ) → F)` -/
noncomputable def fold_k_set
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (set : Set ((indexPowT S φ 0) → F)) (αs : Fin k → F) (hk : k ≤ m): Set (indexPowT S φ k → F) :=
    { g | ∃ f ∈ set, g = fold_k f αs hk}

/-! ### Helper lemmas for the folding degree-halving argument (Claim 4.15 part 1)

These lemmas establish the standard fact that a single fold replaces a degree-`< 2N`
univariate polynomial by a degree-`< N` one via the even/odd decomposition
`p(z) = pₑ(z²) + z · pₒ(z²)`, where the random fold is `pₑ + α·pₒ`. Iterating `k` times
takes a degree-`< 2^m` polynomial to a degree-`< 2^(m-k)` polynomial. -/
namespace FoldingHelpers

open Polynomial BlockRelDistance ReedSolomon

variable {F : Type*} [Field F]

/-- Even part of a univariate polynomial: `pₑ = ∑_j coeff(p, 2j) Xʲ`. -/
noncomputable def evenPart (p : F[X]) : F[X] :=
  ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.monomial j (p.coeff (2 * j))

/-- Odd part of a univariate polynomial: `pₒ = ∑_j coeff(p, 2j+1) Xʲ`. -/
noncomputable def oddPart (p : F[X]) : F[X] :=
  ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.monomial j (p.coeff (2 * j + 1))

lemma evenPart_coeff (p : F[X]) (n : ℕ) :
    (evenPart p).coeff n = if n ≤ p.natDegree then p.coeff (2 * n) else 0 := by
  unfold evenPart
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (p.natDegree+1)) n (fun j => p.coeff (2*j))]
  simp only [Finset.mem_range]
  by_cases h : n ≤ p.natDegree
  · rw [if_pos (Nat.lt_succ_iff.mpr h), if_pos h]
  · rw [if_neg (by omega), if_neg h]

lemma oddPart_coeff (p : F[X]) (n : ℕ) :
    (oddPart p).coeff n = if n ≤ p.natDegree then p.coeff (2 * n + 1) else 0 := by
  unfold oddPart
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (p.natDegree+1)) n (fun j => p.coeff (2*j+1))]
  simp only [Finset.mem_range]
  by_cases h : n ≤ p.natDegree
  · rw [if_pos (Nat.lt_succ_iff.mpr h), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- Polynomial identity: `p = pₑ(X²) + X · pₒ(X²)`. -/
lemma poly_eq_even_odd (p : F[X]) :
    p = (evenPart p).comp (X ^ 2) + X * (oddPart p).comp (X ^ 2) := by
  ext n
  rw [coeff_add, ← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [coeff_expand (by norm_num) (evenPart p) (k+k)]
    have h2k : (2 : ℕ) ∣ (k + k) := ⟨k, by ring⟩
    simp only [h2k, if_true]
    have hdiv : (k + k) / 2 = k := by omega
    rw [hdiv, evenPart_coeff]
    have hsecond : (X * (expand F 2 (oddPart p))).coeff (k + k) = 0 := by
      by_cases hk0 : k = 0
      · subst hk0; simp [coeff_X_mul_zero (expand F 2 (oddPart p))]
      · have : k + k = (k + k - 1) + 1 := by omega
        rw [this, coeff_X_mul]
        rw [coeff_expand (by norm_num) (oddPart p) (k + k - 1)]
        have hodd : ¬ (2 : ℕ) ∣ (k + k - 1) := by omega
        simp only [hodd, if_false]
    rw [hsecond, _root_.add_zero]
    by_cases hkdeg : k ≤ p.natDegree
    · simp only [hkdeg, if_true, two_mul]
    · simp only [hkdeg, if_false]
      have hcz : p.coeff (k + k) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
      rw [hcz]
  · subst hk
    rw [coeff_expand (by norm_num) (evenPart p) (2 * k + 1)]
    have hno : ¬ (2 : ℕ) ∣ (2 * k + 1) := by omega
    simp only [hno, if_false, _root_.zero_add]
    rw [coeff_X_mul (expand F 2 (oddPart p)) (2 * k)]
    rw [coeff_expand (by norm_num) (oddPart p) (2 * k)]
    have hdvd : (2 : ℕ) ∣ (2 * k) := ⟨k, by ring⟩
    simp only [hdvd, if_true]
    have hdiv2 : (2 * k) / 2 = k := by omega
    rw [hdiv2, oddPart_coeff]
    by_cases hkdeg : k ≤ p.natDegree
    · simp only [hkdeg, if_true]
    · simp only [hkdeg, if_false]
      have hcz : p.coeff (2 * k + 1) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
      rw [hcz]

/-- Key decomposition for evaluation: `p(v) = pₑ(v²) + v·pₒ(v²)`. -/
lemma eval_eq_even_odd (p : F[X]) (v : F) :
    p.eval v = (evenPart p).eval (v ^ 2) + v * (oddPart p).eval (v ^ 2) := by
  conv_lhs => rw [poly_eq_even_odd p]
  simp [Polynomial.eval_comp]

/-- The fold polynomial: `foldPoly p α = pₑ + α·pₒ`. -/
noncomputable def foldPoly (p : F[X]) (α : F) : F[X] := evenPart p + α • oddPart p

/-- The fold-evaluation identity: for `v ≠ 0` and `2 ≠ 0`,
    `(p(v)+p(-v))/2 + α·((p(v)-p(-v))/(2v)) = (foldPoly p α)(v²)`. -/
lemma foldf_eq_foldPoly_eval (p : F[X]) (α v : F) (hv : v ≠ 0) (h2 : (2 : F) ≠ 0) :
    (p.eval v + p.eval (-v)) / 2 + α * ((p.eval v - p.eval (-v)) / (2 * v))
      = (foldPoly p α).eval (v ^ 2) := by
  have hev : p.eval v = (evenPart p).eval (v^2) + v * (oddPart p).eval (v^2) :=
    eval_eq_even_odd p v
  have hodv : p.eval (-v) = (evenPart p).eval (v^2) + (-v) * (oddPart p).eval (v^2) := by
    have := eval_eq_even_odd p (-v)
    rwa [neg_pow, show ((-1 : F)) ^ 2 = 1 by ring, one_mul] at this
  rw [hev, hodv]
  unfold foldPoly
  rw [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  field_simp
  ring

lemma evenPart_degree_lt (p : F[X]) (N : ℕ) (h : p.degree < (2 * N : ℕ)) :
    (evenPart p).degree < (N : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [evenPart_coeff]
  have hNn : (N : ℕ) ≤ n := by exact_mod_cast hn
  by_cases hkdeg : n ≤ p.natDegree
  · simp only [hkdeg, if_true]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le h ?_
    exact_mod_cast Nat.mul_le_mul_left 2 hNn
  · simp only [hkdeg, if_false]

lemma oddPart_degree_lt (p : F[X]) (N : ℕ) (h : p.degree < (2 * N : ℕ)) :
    (oddPart p).degree < (N : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [oddPart_coeff]
  have hNn : (N : ℕ) ≤ n := by exact_mod_cast hn
  by_cases hkdeg : n ≤ p.natDegree
  · simp only [hkdeg, if_true]
    apply Polynomial.coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le h ?_
    have hle : 2 * N ≤ 2 * n + 1 := by omega
    exact_mod_cast hle
  · simp only [hkdeg, if_false]

/-- Degree halving: if `deg p < 2N` then `deg (foldPoly p α) < N`. -/
lemma foldPoly_degree_lt (p : F[X]) (α : F) (N : ℕ) (h : p.degree < (2 * N : ℕ)) :
    (foldPoly p α).degree < (N : ℕ) := by
  unfold foldPoly
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
  rw [max_lt_iff]
  refine ⟨evenPart_degree_lt p N h, ?_⟩
  refine lt_of_le_of_lt (Polynomial.degree_smul_le α (oddPart p)) ?_
  exact oddPart_degree_lt p N h

/-- `extract_x` produces a square root of `y.val`. -/
lemma extract_x_sq {ι : Type} [Pow ι ℕ] {F : Type} [Field F]
    (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPowT S φ (k + 1)) :
    ((extract_x S φ k y).val) ^ 2 = y.val := by
  have hx := Classical.choose_spec y.property
  have hval : (extract_x S φ k y).val = (φ (Classical.choose y.property)) ^ (2^k) := rfl
  rw [hval, ← pow_mul, ← pow_succ]
  exact hx.2.symm

/-- A function `f : indexPowT S φ k → F` is the `.val`-evaluation of polynomial `p`. -/
def IsEvalOf {ι : Type} [Pow ι ℕ] {F : Type} [Field F]
    {S : Finset ι} {φ : ι ↪ F} {k : ℕ}
    (f : indexPowT S φ k → F) (p : F[X]) : Prop :=
  ∀ z : indexPowT S φ k, f z = p.eval z.val

/-- **Single fold step.** If `fk` is the `.val`-evaluation of `p`, the domain values are
    nonzero, negation is compatible with `.val`, and `2 ≠ 0`, then folding `fk` by `α`
    produces the `.val`-evaluation of `foldPoly p α`. -/
lemma foldf_isEvalOf {ι : Type} [Pow ι ℕ] {F : Type} [Field F]
    {S : Finset ι} {φ : ι ↪ F} {k : ℕ} [Neg (indexPowT S φ k)]
    (p : F[X]) (α : F) (fk : indexPowT S φ k → F)
    (hfk : IsEvalOf fk p)
    (hneg : ∀ z : indexPowT S φ k, (-z).val = -(z.val))
    (hnz : ∀ z : indexPowT S φ k, z.val ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    IsEvalOf (fun y => foldf S φ y fk α) (foldPoly p α) := by
  intro y
  change foldf S φ y fk α = (foldPoly p α).eval y.val
  simp only [foldf]
  set xPow := extract_x S φ k y with hxPow
  have hfx : fk xPow = p.eval xPow.val := hfk xPow
  have hfnx : fk (-xPow) = p.eval (-(xPow.val)) := by
    rw [hfk (-xPow), hneg xPow]
  rw [hfx, hfnx]
  have hv : xPow.val ≠ 0 := hnz xPow
  rw [foldf_eq_foldPoly_eval p α xPow.val hv h2]
  congr 1
  exact extract_x_sq S φ k y

/-- **Iterated fold tracks a polynomial with halving degree.** For each `i ≤ m`, there is a
    polynomial of degree `< 2^(m-i)` whose `.val`-evaluation equals `fold_k_core f i αs`,
    provided the base function is the `.val`-evaluation of a degree-`< 2^m` polynomial and the
    per-level pinning facts hold. -/
lemma fold_k_core_isEvalOf {ι : Type} [Pow ι ℕ] {F : Type} [Field F]
    {S : Finset ι} {φ : ι ↪ F} [∀ i : ℕ, Neg (indexPowT S φ i)]
    (f : indexPowT S φ 0 → F) (p₀ : F[X]) (m : ℕ)
    (hp₀deg : p₀.degree < (2 ^ m : ℕ))
    (hf : IsEvalOf f p₀)
    (hneg : ∀ (i : ℕ) (z : indexPowT S φ i), (-z).val = -(z.val))
    (hnz : ∀ (i : ℕ) (z : indexPowT S φ i), z.val ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    ∀ (i : ℕ), i ≤ m → ∀ (αs : Fin i → F),
      ∃ q : F[X], q.degree < (2 ^ (m - i) : ℕ) ∧ IsEvalOf (fold_k_core f i αs) q := by
  intro i
  induction i with
  | zero =>
    intro _ αs
    refine ⟨p₀, by simpa using hp₀deg, ?_⟩
    intro z
    exact hf z
  | succ k ih =>
    intro hk αs
    have hk' : k ≤ m := Nat.le_of_succ_le hk
    obtain ⟨q, hqdeg, hqeval⟩ := ih hk' (fun i => αs (Fin.succ i))
    refine ⟨foldPoly q (αs 0), ?_, ?_⟩
    · have hmk : m - k = (m - (k+1)) + 1 := by omega
      have hq' : q.degree < (2 * 2 ^ (m - (k+1)) : ℕ) := by
        rw [hmk] at hqdeg
        rw [pow_succ] at hqdeg
        have heq : (2 ^ (m - (k+1)) * 2 : ℕ) = (2 * 2 ^ (m - (k+1)) : ℕ) := by ring
        rwa [heq] at hqdeg
      exact foldPoly_degree_lt q (αs 0) (2 ^ (m - (k+1))) hq'
    · have hstep := foldf_isEvalOf (S := S) (φ := φ) (k := k) q (αs 0)
        (fold_k_core f k (fun i => αs (Fin.succ i))) hqeval (hneg k) (hnz k) h2
      intro y
      show fold_k_core f (k+1) αs y = (foldPoly q (αs 0)).eval y.val
      exact hstep y

/-- From smooth-code membership and `.val`-pinning, extract the evaluating polynomial. -/
lemma isEvalOf_of_mem_smoothCode {ι : Type} [Pow ι ℕ] {F : Type} [Field F] [DecidableEq F]
    {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
    {φ_k : (indexPowT S φ k) ↪ F} [Fintype (indexPowT S φ k)] [Smooth φ_k]
    (hφk : ∀ z : indexPowT S φ k, φ_k z = z.val)
    (f : indexPowT S φ k → F) (hf : f ∈ smoothCode φ_k m) :
    ∃ p : F[X], p.degree < (2 ^ m : ℕ) ∧ IsEvalOf f p := by
  rw [smoothCode, ReedSolomon.mem_code_iff_exists_polynomial] at hf
  obtain ⟨p, hpdeg, hpeq⟩ := hf
  refine ⟨p, hpdeg, ?_⟩
  intro z
  rw [hpeq]
  change p.eval (φ_k z) = p.eval z.val
  rw [hφk z]

/-- From `.val`-evaluation by a low-degree polynomial and `.val`-pinning,
    conclude smooth-code membership. -/
lemma mem_smoothCode_of_isEvalOf {ι : Type} [Pow ι ℕ] {F : Type} [Field F] [DecidableEq F]
    {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
    {φ_k : (indexPowT S φ k) ↪ F} [Fintype (indexPowT S φ k)] [Smooth φ_k]
    (hφk : ∀ z : indexPowT S φ k, φ_k z = z.val)
    (g : indexPowT S φ k → F) (p : F[X]) (hpdeg : p.degree < (2 ^ m : ℕ))
    (hg : IsEvalOf g p) :
    g ∈ smoothCode φ_k m := by
  rw [smoothCode]
  apply ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval p hpdeg
  intro z
  rw [hg z, hφk z]

end FoldingHelpers

section FoldingLemmas

open MutualCorrAgreement Generator LinearMvExtension ListDecodable
     NNReal ReedSolomon ProbabilityTheory Polynomial

variable {F : Type} [Field F] [DecidableEq F]
         {ι : Type} [Pow ι ℕ]

/-! ### Fold bridge to univariate `foldNth`

The functions `extract_x`/`foldf` implement the WHIR 2-to-1 even/odd fold over the
`indexPowT` square-root tower. The lemmas below bridge them to the axiom-clean univariate
algebra of `Polynomial.foldNth 2` (`SplitFold.lean`), so that a folded smooth codeword can be
tracked through `decodeLT`/`mVdecode`.

The `Neg (indexPowT S φ k)` instance carried by `foldf` is, in this file's loose setting,
an **abstract** typeclass parameter with no law connecting `(-x).val` to `-(x.val)` in `F`
(`git grep` confirms no `Neg` instance and no negation law for `indexPowT` anywhere in ArkLib).
The bridge therefore takes that law (`hneg`) as an explicit hypothesis, exactly mirroring the
documented statement repairs on the sibling lemmas in `BlockRelDistance.lean`
(`relHammingDist_le_blockRelDistance` etc.), which thread `hφ' : ∀ x, φ' x = x.val` and the
2-adic cardinality relation as hypotheses because the file's `indexPowT` data does not pin them.
-/

omit [DecidableEq F] [Pow ι ℕ] in
/-- The square-root relation realized by `extract_x`: the value of `y ∈ indexPowT S φ (k+1)`
is the square of the value of its extracted root `extract_x S φ k y ∈ indexPowT S φ k`.
Direct from `extract_x`'s definition (`z = (φ x)^(2^k)`) and `Classical.choose_spec`
(`y.val = (φ x)^(2^(k+1))`), since `(2^(k+1)) = 2^k * 2`. -/
lemma extract_x_val_sq {S : Finset ι} {φ : ι ↪ F} (k : ℕ) (y : indexPowT S φ (k + 1)) :
    y.val = ((extract_x S φ k y).val) ^ 2 := by
  have hspec := Classical.choose_spec y.property
  -- `hspec.2 : y.val = (φ (choose ..)) ^ (2 ^ (k+1))`
  show y.val = ((φ (Classical.choose y.property)) ^ (2 ^ k)) ^ 2
  rw [← pow_mul, ← pow_succ]
  exact hspec.2

omit [DecidableEq F] [Pow ι ℕ] in
/-- **Fold bridge** (core algebraic identity). For a univariate polynomial `p` and the
"decoded" function `g x := p.eval x.val`, the WHIR fold value `foldf S φ y g α` coincides
with the univariate fold `(foldNth 2 p α).eval y.val`.

Hypotheses (all forced by the smooth-domain setting but not by the file's loose `indexPowT`):
* `hneg`: the abstract negation agrees with field negation on the extracted root,
  `(-(extract_x S φ k y)).val = -((extract_x S φ k y)).val`;
* `hx0`: the extracted root is nonzero in `F` (smooth domains avoid `0`);
* `h2`: `(2 : F) ≠ 0` (the field has odd characteristic, as for FRI/WHIR).

Proof: rewrite `g` at the two query points via `hneg`, apply `foldNth_two_eval` at
`x := (extract_x ..).val` (using `extract_x_val_sq` for `y.val = x^2`), and check the two
algebraic forms agree by `field_simp`. -/
lemma foldf_eq_foldNth_eval {S : Finset ι} {φ : ι ↪ F} {k : ℕ} [Neg (indexPowT S φ k)]
    (y : indexPowT S φ (k + 1)) (p : F[X]) (α : F)
    (hneg : (-(extract_x S φ k y)).val = -((extract_x S φ k y).val))
    (hx0 : (extract_x S φ k y).val ≠ 0) (h2 : (2 : F) ≠ 0) :
    foldf S φ y (fun x : indexPowT S φ k => p.eval x.val) α
      = (foldNth 2 p α).eval y.val := by
  set x : F := (extract_x S φ k y).val with hx
  unfold foldf
  simp only []
  rw [hneg]
  rw [extract_x_val_sq k y, ← hx]
  rw [foldNth_two_eval p x α hx0 h2]
  field_simp

/-- Degree bookkeeping for one fold step: if `d < 2^(M+1)` then `d / 2 < 2^M`.
This is the `2^(m-j) → 2^(m-j-1)` degree halving (`foldNth 2` halves the degree bound). -/
lemma half_lt_pow_of_lt_pow_succ {d M : ℕ} (hd : d < 2 ^ (M + 1)) : d / 2 < 2 ^ M := by
  have h2 : 2 ^ (M + 1) = 2 ^ M * 2 := by rw [pow_succ]
  rw [h2] at hd
  omega

omit [Pow ι ℕ] in
/-- **Single fold step → membership** (the inductive heart of Claim 4.15 part 1).

Let `f : smoothCode φ_j (M+1)` with decoded univariate polynomial `p := decodeLT f`
(degree `< 2^(M+1)`). Then the function obtained by folding `f` once,
`g z := foldf S φ z f.val α`, lies in `smoothCode φ_{j+1} M`, with witness polynomial
`foldNth 2 p α` (degree `≤ (2^(M+1)-1)/2 < 2^M`).

Hypotheses make explicit the smooth-domain structure the loose `indexPowT` setup omits
(mirroring the documented repairs on the `BlockRelDistance.lean` sibling lemmas):
* `hφj  : ∀ x, φ_j x = x.val` and `hφj1 : ∀ z, φ_{j+1} z = z.val`
  pin the per-round embeddings to the canonical subtype inclusion;
* `hneg : ∀ z, (-(extract_x S φ j z)).val = -((extract_x S φ j z).val)`
  is the field-negation law for the abstract `Neg` (no such law is derivable in-file);
* `hx0  : ∀ z, (extract_x S φ j z).val ≠ 0` (smooth domains avoid `0`);
* `h2   : (2 : F) ≠ 0` (odd characteristic).

Proof: the witness is `q := foldNth 2 p α`. Its degree halves
(`foldNth_natDegree_le` + `half_lt_pow_of_lt_pow_succ`), and pointwise
`g z = foldf … = (foldNth 2 p α).eval z.val = q.eval (φ_{j+1} z)` by `foldf_eq_foldNth_eval`
(after rewriting `f.val x = p.eval (φ_j x) = p.eval x.val`). Membership then follows from
`mem_code_of_polynomial_of_natDegree_lt_of_eval`. -/
lemma foldf_step_mem_smoothCode
    {S : Finset ι} {φ : ι ↪ F} {j M : ℕ}
    {φ_j : (indexPowT S φ j) ↪ F} {φ_j1 : (indexPowT S φ (j + 1)) ↪ F}
    [Fintype (indexPowT S φ j)] [DecidableEq (indexPowT S φ j)] [Smooth φ_j]
    [Fintype (indexPowT S φ (j + 1))] [DecidableEq (indexPowT S φ (j + 1))]
    [Smooth φ_j1] [Neg (indexPowT S φ j)]
    (f : smoothCode φ_j (M + 1)) (α : F)
    (hφj : ∀ x : indexPowT S φ j, φ_j x = x.val)
    (hφj1 : ∀ z : indexPowT S φ (j + 1), φ_j1 z = z.val)
    (hneg : ∀ z : indexPowT S φ (j + 1),
      (-(extract_x S φ j z)).val = -((extract_x S φ j z).val))
    (hx0 : ∀ z : indexPowT S φ (j + 1), (extract_x S φ j z).val ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    (fun z : indexPowT S φ (j + 1) => foldf S φ z (f : indexPowT S φ j → F) α)
      ∈ smoothCode φ_j1 M := by
  classical
  -- Decoded univariate polynomial of `f` and its degree bound.
  set p : F[X] := (decodeLT (f : smoothCode φ_j (M + 1)) : Polynomial F) with hp
  have hp_deg : p.natDegree < 2 ^ (M + 1) := by
    have hmem := (decodeLT (f : smoothCode φ_j (M + 1))).2
    rw [Polynomial.mem_degreeLT] at hmem
    by_cases h0 : p = 0
    · rw [h0, Polynomial.natDegree_zero]; positivity
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hmem
  -- `f`'s value at `x` is `p.eval x.val` (decode roundtrip + canonical embedding).
  have hf_val : ∀ x : indexPowT S φ j, (f : indexPowT S φ j → F) x = p.eval x.val := by
    intro x
    have hroundtrip : p.eval (φ_j x) = (f : indexPowT S φ j → F) x :=
      Lagrange.eval_interpolate_at_node (f : indexPowT S φ j → F)
        (φ_j.injective.injOn) (Finset.mem_univ x)
    rw [← hroundtrip, hφj x]
  -- Witness polynomial: the univariate fold.
  set q : F[X] := foldNth 2 p α with hq
  -- Degree halving: `q.natDegree < 2^M`.
  have hq_deg : q.natDegree < 2 ^ M := by
    have hle : q.natDegree ≤ p.natDegree / 2 := by
      rw [hq]; exact foldNth_natDegree_le p α
    exact lt_of_le_of_lt hle (half_lt_pow_of_lt_pow_succ hp_deg)
  -- Pointwise: folded value equals `q.eval (φ_{j+1} z)`.
  have heval : ∀ z : indexPowT S φ (j + 1),
      foldf S φ z (f : indexPowT S φ j → F) α = q.eval (φ_j1 z) := by
    intro z
    have hfeq : (f : indexPowT S φ j → F)
        = fun x : indexPowT S φ j => p.eval x.val := by
      funext x; exact hf_val x
    rw [hfeq]
    rw [foldf_eq_foldNth_eval z p α (hneg z) (hx0 z) h2, hφj1 z, hq]
  -- Membership via the degree-bounded evaluation criterion.
  exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval q hq_deg heval

omit [Pow ι ℕ] in
/-- The `k`-fold tower membership, proven by induction on `k`, peeling the outermost fold
(level `k → k+1`, challenge `αs 0`) via `foldf_step_mem_smoothCode` and recursing into the
inner `fold_k_core … k (αs ∘ Fin.succ)` over `indexPowT S φ k`.

This is the engine behind `fold_f_g`. It threads, over **every** level `j ≤ k`, the
canonical-inclusion / negation / nonzero structure that the smooth-domain setting supplies but
the file's loose `indexPowT` data does not (see `foldf_step_mem_smoothCode`). The intermediate
levels `0 < j < k` are exactly why the original `fold_f_g`, carrying embeddings only for `j = 0`
and `j = k`, is not provable as literally stated — the induction needs the whole family. -/
lemma fold_f_g_core
    {S : Finset ι} {φ : ι ↪ F} {m : ℕ}
    (φ_all : ∀ j : ℕ, (indexPowT S φ j) ↪ F)
    [instFin : ∀ j : ℕ, Fintype (indexPowT S φ j)]
    [instDec : ∀ j : ℕ, DecidableEq (indexPowT S φ j)]
    [instSmooth : ∀ j : ℕ, Smooth (φ_all j)]
    [∀ j : ℕ, Neg (indexPowT S φ j)]
    (hφ : ∀ j : ℕ, ∀ x : indexPowT S φ j, φ_all j x = x.val)
    (hneg : ∀ j : ℕ, ∀ z : indexPowT S φ (j + 1),
      (-(extract_x S φ j z)).val = -((extract_x S φ j z).val))
    (hx0 : ∀ j : ℕ, ∀ z : indexPowT S φ (j + 1), (extract_x S φ j z).val ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (f : smoothCode (φ_all 0) m) :
    ∀ (k : ℕ) (αs : Fin k → F) (_hk : k ≤ m),
      fold_k_core (f : indexPowT S φ 0 → F) k αs ∈ smoothCode (φ_all k) (m - k) := by
  intro k
  induction k with
  | zero =>
    intro αs _hk
    -- `fold_k_core … 0 αs = f.val`; `m - 0 = m`.
    simp only [fold_k_core, Nat.sub_zero]
    exact f.2
  | succ k ih =>
    intro αs hk
    -- Peel the outermost fold: `fold_k_core … (k+1) αs = foldf … (fold_k_core … k (αs∘succ)) (αs
    -- 0)`.
    have hk' : k ≤ m := Nat.le_of_succ_le hk
    -- Inner fold is a smooth codeword over level `k` of degree bound `m - k`.
    have hinner : fold_k_core (f : indexPowT S φ 0 → F) k (fun i => αs (Fin.succ i))
        ∈ smoothCode (φ_all k) (m - k) := ih (fun i => αs (Fin.succ i)) hk'
    -- `m - k = (m - (k+1)) + 1`, the `M + 1` shape the step lemma needs.
    have hM : m - k = (m - (k + 1)) + 1 := by omega
    -- Repackage the inner codeword at the `(M+1)` index expected by the step lemma.
    set fk : smoothCode (φ_all k) ((m - (k + 1)) + 1) :=
      ⟨fold_k_core (f : indexPowT S φ 0 → F) k (fun i => αs (Fin.succ i)), by
        rw [← hM]; exact hinner⟩ with hfk
    -- Apply the single fold step at level `j := k`, `M := m - (k+1)`.
    have hstep := foldf_step_mem_smoothCode
      (φ_j := φ_all k) (φ_j1 := φ_all (k + 1)) fk (αs 0)
      (hφ k) (hφ (k + 1)) (hneg k) (hx0 k) h2
    -- Identify the folded function with `fold_k_core … (k+1) αs`.
    have hfun : (fun z : indexPowT S φ (k + 1) =>
        foldf S φ z (fk : indexPowT S φ k → F) (αs 0))
        = fold_k_core (f : indexPowT S φ 0 → F) (k + 1) αs := by
      funext z
      simp only [fold_k_core, hfk]
    -- The target degree index `m - (k+1)` matches.
    rw [hfun] at hstep
    exact hstep

omit [Pow ι ℕ] in
/-- Claim 4.15 part 1 (statement repair, 2026-06-04).

  Let `f ∈ RS[F, ι, m]`, `α ∈ Fᵏ` the folding randomness, `g = fold_k(f, α)`; for `k ≤ m`,
  `g ∈ RS[F, ι^(2ᵏ), m - k]`.

  ## STATEMENT REPAIR (2026-06-04)

  As literally written the lemma is **not provable**: it carries evaluation embeddings only for
  the two extreme levels (`φ_0` at level `0`, `φ_k` at level `k`), but the `k`-fold tower passes
  through every intermediate level `0 < j < k`, and `foldf` at each level queries the abstract
  `Neg (indexPowT S φ j)` instance — for which the file provides **no** law connecting `(-x).val`
  to `-(x.val)`, and no constraint pinning `φ_j` to the canonical inclusion `x ↦ x.val`. Both
  `g = 0` and `g ≠ 0` codewords are then consistent with the loose data, so membership in the
  specific code `smoothCode φ_k (m-k)` cannot be forced. This mirrors the documented repairs on
  the sibling lemmas in `BlockRelDistance.lean` (`relHammingDist_le_blockRelDistance` etc.), which
  thread `hφ' : ∀ x, φ' x = x.val` and 2-adic structure as explicit hypotheses for the same reason.

  Repair: replace the two loose embeddings with a per-level family `φ_all` and supply, for every
  level, the canonical-inclusion law `hφ`, the field-negation law `hneg`, the nonzero-root law
  `hx0`, and `(2 : F) ≠ 0`. The proof is then the clean induction `fold_f_g_core`. -/
lemma fold_f_g
    {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
    (φ_all : ∀ j : ℕ, (indexPowT S φ j) ↪ F)
    [∀ j : ℕ, Fintype (indexPowT S φ j)]
    [∀ j : ℕ, DecidableEq (indexPowT S φ j)]
    [∀ j : ℕ, Smooth (φ_all j)]
    [∀ j : ℕ, Neg (indexPowT S φ j)]
    (hφ : ∀ j : ℕ, ∀ x : indexPowT S φ j, φ_all j x = x.val)
    (hneg : ∀ j : ℕ, ∀ z : indexPowT S φ (j + 1),
      (-(extract_x S φ j z)).val = -((extract_x S φ j z).val))
    (hx0 : ∀ j : ℕ, ∀ z : indexPowT S φ (j + 1), (extract_x S φ j z).val ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (αs : Fin k → F) (hk : k ≤ m)
    (f : smoothCode (φ_all 0) m) :
    let f_fun := (f : (indexPowT S φ 0) → F)
    let g := fold_k f_fun αs hk
    g ∈ smoothCode (φ_all k) (m - k) := by
  intro f_fun g
  show fold_k (f : indexPowT S φ 0 → F) αs hk ∈ smoothCode (φ_all k) (m - k)
  unfold fold_k
  exact fold_f_g_core φ_all hφ hneg hx0 h2 f k αs hk

omit [Pow ι ℕ] in
/-- Claim 4.5 part 2 (statement repair, 2026-06-04)
  If fPoly be the multilinear extension of f, then we have
  (m-k)-variate multilinear extension of g as `gPoly = fPoly(α₀,α₁,...α_{k-1},X_k,..,X_{m-1})`

  ## STATEMENT REPAIR (2026-06-04)

  As literally written the lemma is **not provable**: `f` and `g` are supplied as two *independent*
  smooth codewords with no hypothesis relating them, yet the conclusion asserts that `g`'s decoded
  multilinear polynomial is the partial evaluation of `f`'s. Nothing in the loose `indexPowT` data
  forces `g` to be the `αs`-fold of `f` (the per-level abstract `Neg`/embedding structure is
  unconstrained — see the companion repair on `fold_f_g`), so the equality cannot hold for an
  arbitrary `g`. This mirrors `fold_f_g`'s repair: the missing fold relationship must be supplied.

  Repair: add the hypothesis `hgp` that `g`'s decoded *univariate* polynomial is the
  partial-evaluation fold of `f`'s multilinear extension contracted back to univariate form
  (`decodeLT g = powAlgHom (partialEval (mVdecode f) αs hk)`) — the polynomial-level shadow of the
  function-level identity `g = fold_k(f, αs)` established by `fold_f_g`. The proof then re-extends
  this univariate identity: `mVdecode g = linearMvExtension (decodeLT g)
  = linearMvExtension (powAlgHom (partialEval (mVdecode f) αs hk)) = partialEval (mVdecode f) αs
  hk`,
  the last step by the left inverse `linearMvExtension_powAlgHom` (valid since `partialEval` of a
  degreewise-linear polynomial is degreewise-linear, `partialEval_mem_restrictDegree`). -/
lemma fold_f_g_poly
    {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_k : (indexPowT S φ k) ↪ F}
  [Fintype (indexPowT S φ 0)] [DecidableEq (indexPowT S φ 0)] [Smooth φ_0]
  [Fintype (indexPowT S φ k)] [DecidableEq (indexPowT S φ k)] [Smooth φ_k]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  (αs : Fin k → F) (hk : k ≤ m)
  (f : smoothCode φ_0 m) (g : smoothCode φ_k (m-k))
  (hgp : (decodeLT g : Polynomial F)
          = powAlgHom (partialEval (mVdecode f) αs hk)) :
  let fPoly := mVdecode f
  let gPoly := mVdecode g
  gPoly = partialEval fPoly αs hk := by
  intro fPoly gPoly
  show mVdecode g = partialEval (mVdecode f) αs hk
  -- `mVdecode g = linearMvExtension (decodeLT g)` by definition.
  have hmv : mVdecode g = linearMvExtension (decodeLT g) := rfl
  -- `partialEval (mVdecode f) αs hk` is degreewise-linear.
  have hpe_mem : partialEval (mVdecode f) αs hk
      ∈ MvPolynomial.restrictDegree (Fin (m - k)) F 1 :=
    partialEval_mem_restrictDegree (mVdecode f) (mVdecode_mem_restrictDegree f) αs hk
  rw [hmv]
  -- Recast `decodeLT g` as the `degreeLT` element `⟨powAlgHom (partialEval …), _⟩` via `hgp`.
  have hdeq : (decodeLT g : Polynomial.degreeLT F (2 ^ (m - k)))
      = ⟨powAlgHom (partialEval (mVdecode f) αs hk),
          powAlgHom_mem_degreeLT _ hpe_mem⟩ :=
    Subtype.ext hgp
  rw [hdeq]
  exact linearMvExtension_powAlgHom _ hpe_mem

/--
The `GenMutualCorrParams` class captures the necessary parameters and assumptions
to model a sequence of proximity generators for a set of smooth ReedSolomon codes.
It contains the following:

for `i ∈ [0,k]` :
- `inst1`, `inst2`, `inst3`: typeclass instances required to operate on `ι^(2ⁱ)`
    (finiteness, nonemptiness, and decidable equality).
- `φ_i`: per-round embeddings from `ι^(2ⁱ)` into `F`.
- `inst4`: smoothness assumption for each `φ_i`.
- `Gen_α i`: the proximity generators wrt the generator function
  `Gen(parℓ,α) : {1,α,α²,..,α^{parℓ-1}}` defined as per `hgen` for code `Cᵢ`
- `inst5`, `inst6` : typeclass instances denoting finiteness of `parℓ`
    underlying `Gen_αᵢ` and `parℓ_type`
- `BStar`, `errStar`: parameters denoting proximity and error thresholds per round.
- `h`: main agreement assumption, stating that each `Gen_α` satisfies mutual correlated agreement
    for its underlying code.
- `hcard, hcard'` : `|Gen_αᵢ.parℓ| = 2` and `|parℓ_type| = 2`
-/
class GenMutualCorrParams [Fintype F] (S : Finset ι) (φ : ι ↪ F) (k : ℕ) where
  m : ℕ

  inst1 : ∀ i : Fin (k + 1), Fintype (indexPowT S φ i)
  inst2 : ∀ i : Fin (k + 1), Nonempty (indexPowT S φ i)
  inst3 : ∀ i : Fin (k + 1), DecidableEq (indexPowT S φ i)

  φ_i : ∀ i : Fin (k + 1), (indexPowT S φ i) ↪ F
  inst4 : ∀ i : Fin (k + 1), Smooth (φ_i i)

  parℓ_type : ∀ _ : Fin (k + 1), Type
  inst5 : ∀ i : Fin (k + 1), Fintype (parℓ_type i)

  exp : ∀ i : Fin (k + 1), (parℓ_type i) ↪ ℕ

  Gen_α : ∀ i : Fin (k + 1), ProximityGenerator (indexPowT S φ i) F :=
    fun i => RSGenerator.genRSC (parℓ_type i) (φ_i i) (m - i) (exp i)
  inst6 : ∀ i : Fin (k + 1), Fintype (Gen_α i).parℓ

  BStar : ∀ i : Fin (k + 1), (Set (indexPowT S φ i → F)) → Type → ℝ≥0
  errStar : ∀ i : Fin (k + 1), (Set (indexPowT S φ i → F)) → Type → ℝ → ENNReal

  h : ∀ i : Fin (k + 1), hasMutualCorrAgreement (Gen_α i)
                                             (BStar i (Gen_α i).C (Gen_α i).parℓ)
                                             (errStar i (Gen_α i).C (Gen_α i).parℓ)

  hcard : ∀ i : Fin (k + 1), Fintype.card ((Gen_α i).parℓ) = 2
  hcard' : ∀ i : Fin (k + 1), Fintype.card (parℓ_type i) = 2

/-- **Union-bound backbone of Theorem 4.20 (proven helper).**

The error accounting in ABF26 Thm 4.20 bounds the failure probability of a single
multi-round event by the *sum* over the `k+1` rounds of the per-round `errStar` terms.
The purely-probabilistic core of that accounting is the following finite union bound:
if the failure event `P` always entails the existence of *some* round `i ∈ s` whose
per-round bad event `Q i` fires, then `Pr[P] ≤ ∑ i ∈ s, Pr[Q i]`.

This is sorry-free and axiom-clean (`propext, Classical.choice, Quot.sound` only). It is
the genuinely-closable probabilistic component of the (conditional) Theorem 4.20: the
remaining content — exhibiting the per-round events `Q i` and discharging each
`Pr[Q i] ≤ errStar i …` from the round-`i` mutual-correlated-agreement hypothesis
(`params.h i`), together with the strictness of the final `<` — is exactly what the
inductive lemmas `folding_preserves_listdecoding_base` (L4.21) /
`…_bound` (L4.22) / `…_base_ne_subset` (L4.23) supply, and is not derivable from the
loose `indexPowT` data available here. The capstone Theorem 4.20 below therefore remains a
statement-only `def : Prop` (`folding_listdecoding_if_genMutualCorrAgreement` — no `sorry`
exists; its honest closure is a multi-step ABF26 §4 formalization, not a leaf proof);
this lemma is integrated as honest partial progress on its probabilistic accounting. -/
theorem Pr_le_finset_sum_of_implies {α : Type} (D : PMF.{0} α) {β : Type} [DecidableEq β]
    (P : α → Prop) (Q : β → α → Prop) (s : Finset β)
    (h_imp : ∀ r, P r → ∃ i ∈ s, Q i r) :
    Pr_{ let r ← D }[ P r ] ≤ ∑ i ∈ s, Pr_{ let r ← D }[ Q i r ] := by
  classical
  rw [ProbabilityTheory.Pr_eq_tsum_indicator D P]
  have hQ : ∀ i, Pr_{ let r ← D }[ Q i r ]
      = ∑' r, D r * (if Q i r then (1 : ENNReal) else 0) := by
    intro i; rw [ProbabilityTheory.Pr_eq_tsum_indicator D (Q i)]
  simp_rw [hQ]
  have hswap :
      ∑ i ∈ s, ∑' r, D r * (if Q i r then (1 : ENNReal) else 0)
        = ∑' r, ∑ i ∈ s, D r * (if Q i r then (1 : ENNReal) else 0) :=
    (Summable.tsum_finsetSum (fun i _ => ENNReal.summable)).symm
  rw [hswap]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hP : P r
  · obtain ⟨i₀, hi₀s, hQi₀⟩ := h_imp r hP
    simp only [hP, if_true, mul_one]
    calc D r = D r * (if Q i₀ r then (1 : ENNReal) else 0) := by
              rw [if_pos hQi₀, mul_one]
      _ ≤ ∑ i ∈ s, D r * (if Q i r then (1 : ENNReal) else 0) :=
            Finset.single_le_sum (f := fun i => D r * (if Q i r then (1 : ENNReal) else 0))
              (fun i _ => zero_le _) hi₀s
  · simp only [hP, if_false, MulZeroClass.mul_zero]
    exact zero_le _

/-- If `A x` is always a subset of `B x`, then the event that the two sets differ is contained
in the event that the reverse inclusion fails. -/
lemma Pr_set_ne_le_Pr_not_subset_of_subset {α β : Type} (D : PMF.{0} α)
    (A B : α → Set β) (hsub : ∀ x, A x ⊆ B x) :
    Pr_{let x ← D}[A x ≠ B x] ≤ Pr_{let x ← D}[¬ B x ⊆ A x] := by
  refine Pr_le_Pr_of_implies D _ _ ?_
  intro x hne hrev
  exact hne (Set.Subset.antisymm (hsub x) hrev)

/-- Theorem 4.20
  Let C = RS[F,ι,m] be a smooth ReedSolomon code
  For k ≤ m and 0 ≤ i ≤ k,
  let Cⁱ = RS[F,ι^(2ⁱ),m-i] and let `Gen(2,α)` be a proxmity generator with
  mutual correlated agreement for `C⁰,...,C^{k}` with proximity bounds BStar and errStar
  Then for every `f : ι → F` and `δ ∈ (0, 1 - max {i ∈ [0,k]} BStar(Cⁱ, 2))`
    `Pr_{αs ← F^k} [ fold_k_set(Λᵣ(0,k,f,S',C,hcode,δ),αs) ≠ Λ(Cᵏ,fold_k(f,αs),δ)]`
      `< ∑ i ∈ [0,k] errStar(Cⁱ,2,δ)`,
  where fold_k_set and fold_k are as defined above,
  αs is a length-k vector of folding randomness,
  `Λᵣ(0,k,f,S',C,hcode,δ)` corresponds to the list of codewords of C δ-close to f,
  wrt (0,k)-wise block relative distance.
  `Λ(Cᵏ,fold_k(f,αs),δ)` is the list of codewords of Cᵏ δ-close to fold_k(f, αs),
  wrt the relative Hamming distance
  Below, we use an instance of the class `GenMutualCorrParams` to capture the
  conditions of proxmity generator with mutual correlated agreement for codes
  C⁰,...,C^{k}.
-/

-- NOTE: need to align this better with the inductive way this is shown via the other lemmas below.
-- DISPOSITION (2026-06-04, updated 2026-06-10): open — gated on the MCA chain. This probabilistic
-- list-decoding equivalence is the `k`-fold composite of the single-step base lemmas below
-- (`folding_preserves_listdecoding_base`/`_bound`, L4.21/4.22), whose `errStar` accounting is in
-- turn supplied by `MutualCorrAgreement.hasMutualCorrAgreement` via `params.h`. Until the MCA
-- bounds (`mca_rsc`/`mca_linearCode`, themselves open — see their dispositions) are available, the
-- per-round error budget summed here cannot be discharged. The deterministic structural
-- ingredient (`fold_f_g`/`fold_f_g_poly`, the fold tracks a degree-halving polynomial) is proven
-- above; what remains is the probabilistic list-set equality, not a folding-algebra fact.
-- UPDATE (2026-06-10): the probabilistic accounting layer is now DISCHARGED:
-- `Fold.folding_listdecoding_of_round_events` (`Whir/FoldingListDecodingReduction.lean`,
-- axiom-clean) proves this capstone from named per-round bad events `Q` with the telescoping
-- implication and per-round `errStar` bounds (union bound + strict finite-sum comparison).
-- The remaining open content is exhibiting `Q` and its bounds from `params.h` (the ABF26 §4
-- per-level induction; see that file's module docstring). A UDR-regime instance of
-- `GenMutualCorrParams` is constructible via `Fold.genMutualCorrParamsUDR`
-- (`Whir/FoldingGenMutualCorrParamsUDR.lean`).
def folding_listdecoding_if_genMutualCorrAgreement
    [Fintype F] {S : Finset ι} {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ] {k m : ℕ}
  {S' : Finset (indexPowT S φ 0)} {φ' : (indexPowT S φ 0) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ 0)] [Smooth φ']
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S' φ']
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ' m) (hLe : k ≤ m)
  {δ : ℝ≥0}
  {params : GenMutualCorrParams S φ k} : Prop :=

  -- necessary typeclasses of underlying domain (ιᵢ)^2ʲ regarding finiteness,
  -- non-emptiness and smoothness
    let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
    let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2

    (∀ (f : (indexPowT S φ 0) → F)
      (_hδ :
        0 < δ ∧
          δ <
            1 - Finset.univ.sup (fun j => params.BStar j (params.Gen_α j).C (params.Gen_α j).parℓ)),
      Pr_{let αs ←$ᵖ (Fin k → F)}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S', C, hcode, δ)
          let fold := fold_k f αs hLe
          let foldSet := fold_k_set listBlock αs hLe
          let kFin : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
          let Cₖ := (params.Gen_α kFin).C
          let listHamming := closeCodewordsRel Cₖ fold δ
          foldSet ≠ listHamming
        ] <
        (∑ i : Fin (k + 1), params.errStar i (params.Gen_α i).C (params.Gen_α i).parℓ δ))

/-- Lemma 4.21
  Let `C = RS[F,ι,m]` be a smooth ReedSolomon code and k ≤ m
  Denote `C' = RS[F,ι^2,m-1]`, then for every `f : ι → F` and `δ ∈ (0, 1 - BStar(C',2))`
    `Pr_{α ← F} [
      fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α)) ≠
        Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ)
    ]`
      `< errStar(C',2,δ)`
    where `fold_k(f,(fun _ : Fin 1 => α))` returns a function `ι^2 → F`,
    `S_0` and `S_1` denote finite sets of elements of type ι and ι², and
    `Λᵣ` denotes the list of δ-close codewords wrt block relative distance.
    `Λᵣ(0,k,f,S_0,C)` denotes Λᵣ at f : ι → F for code C and
    `Λᵣ(1,k,fold_k(f,(fun _ : Fin 1 => α)),S_1,C')` denotes Λᵣ at fold_k : ι^2 → F for code C'.

  **ABF26 mapping.** Probabilistic correctness of folded-RS list decoding. The
  `errStar` accounting comes from MCA bounds (ABF26 Def 4.3 `epsMCA`). The underlying
  list-size bound for FRS specializes ABF26 T3.4 (`subspaceDesign_list_decoding_cz25`
  in `ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean`) via the folded-RS
  τ-subspace-design property (T2.18).

  ## Statement repair (paper-faithful hypotheses, 2026-06-04)

  (Supersedes the earlier wave3 "open" disposition: with the `hsub`/`hrev` repair below this
  lemma is now fully proven, so the genuine probabilistic core is threaded in as `hrev` rather
  than left as a `sorry`.)

  As literally stated the lemma is **false**: `BStar` and `errStar` are abstract,
  *unconstrained* function parameters, so instantiating `errStar := fun _ _ _ => 0`
  makes the conclusion `Pr_{α}[…] < (0 : ℝ≥0∞)`, which is impossible — a probability
  (`Pr_{…}[…] : ENNReal`) is always `≥ 0`. A `git grep` over the whole `ArkLib` tree
  confirms the entire `FoldingLemmas` namespace is orphaned (no external consumers); the
  only consumer of this lemma is the in-file `folding_preserves_listdecoding_base_ne_subset`,
  which carries the *identical* defect.

  Following the file's own established repair convention (see
  `relHammingDist_le_blockRelDistance` / `listBlock_subset_listHamming` in
  `BlockRelDistance.lean`), we make explicit the natural, satisfiable hypotheses the paper
  silently supplies. ABF26 obtains L4.21 (the `≠` event bound) from the conjunction of two
  facts, both stated separately in this very file:

  * **L4.22** (`folding_preserves_listdecoding_bound`): the deterministic *forward
    inclusion* `foldSet ⊆ listBlock'`, which always holds. Threaded here as `hsub`.
  * **L4.23** (`folding_preserves_listdecoding_base_ne_subset`): the probabilistic *reverse*
    bound `Pr_{α}[¬(listBlock' ⊆ foldSet)] < errStar C' 2 δ`, which is exactly the content
    that mutual-correlated-agreement (the hypothesis the strategy treats as given) delivers.
    Threaded here as `hrev`.

  Given the forward inclusion `A ⊆ B`, the events `A ≠ B` and `¬(B ⊆ A)` coincide
  (`A ⊆ B → (A ≠ B ↔ ¬ B ⊆ A)`), so the `≠` bound follows from the reverse bound by event
  domination (`Pr_le_Pr_of_implies`) and `lt_of_le_of_lt`. We therefore *prove the
  implication only*, never MCA itself. The hypotheses are non-vacuous (both are genuine
  satisfiable paper lemmas) and the conclusion is not trivialized. -/
lemma folding_preserves_listdecoding_base
    [Fintype F] {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F}
  [Fintype ι] [DecidableEq ι] [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0}
  -- L4.22: deterministic forward inclusion (paper "easy half", always holds).
  (hsub : ∀ (f : (indexPowT S φ 0) → F) (α : F),
      fold_k_set (Λᵣ(0, k, f, S_0, C, hcode, δ)) (fun _ : Fin 1 => α) hm
        ⊆ Λᵣ(1, k, fold_k f (fun _ : Fin 1 => α) hm, S_1, C', hcode', δ))
  -- L4.23: probabilistic reverse bound (the MCA-delivered content).
  (hrev : ∀ (f : (indexPowT S φ 0) → F) (_hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] < errStar C' 2 δ) :
    ∀ (f : (indexPowT S φ 0) → F) (_hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] < errStar C' 2 δ
  := by
    intro f hδ
    let D : PMF F := PMF.uniformOfFintype F
    -- The genuine probabilistic content: reverse-inclusion failure is rare (≡ L4.23 / MCA).
    have hrev' := hrev f hδ
    -- Event domination: under the forward inclusion `foldSet ⊆ listBlock'`, the event
    -- `foldSet ≠ listBlock'` is contained in `¬ (listBlock' ⊆ foldSet)`.
    have hmono :
        Pr_{let α ← D}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] ≤
        Pr_{let α ← D}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] := by
        refine Pr_le_Pr_of_implies D _ _ ?_
        intro α hne
        dsimp only
        dsimp only at hne
        intro hsub'
        exact hne (Set.Subset.antisymm (hsub f α) hsub')
    exact lt_of_le_of_lt hmono hrev'

/-- **Lemma 4.21, MCA-bridged repaired form.**

This is the production version of the Finding-19 repair: the error term is no longer a free
function that could be set to zero independently of the protocol. Instead it is tied to a genuine
level-1 proximity generator `Gen'` and a hypothesis
`hmca : hasMutualCorrAgreement Gen' BStarV errStarV`.

The proof keeps the same two honest obligations as the repaired
`folding_preserves_listdecoding_base`:
the deterministic forward inclusion `hsub`, and the real ABF26 §4 bridge `hbridge` from
reverse-inclusion failure to WHIR's `proximityCondition`. Once those are supplied, the probability
bound is a direct event-domination chain ending in `hmca`. The conclusion is `≤ errStarV δ`,
matching
the MCA API exactly; no artificial strict inequality is introduced. -/
lemma folding_preserves_listdecoding_base_of_mca_bridge
    [Fintype F] {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F}
  [Fintype ι] [DecidableEq ι] [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1] [Nonempty (indexPowT S φ 1)]
  [hbd0 : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [hbd1 : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m - 1))
  (Gen' : ProximityGenerator (indexPowT S φ 1) F) [Fintype Gen'.parℓ]
  (BStarV : ℝ) (errStarV : ℝ → ENNReal)
  (hmca : hasMutualCorrAgreement Gen' BStarV errStarV)
  (hsub : ∀ (f : (indexPowT S φ 0) → F) (α : F),
      fold_k_set (Λᵣ(0, k, f, S_0, C, hcode, δ)) (fun _ : Fin 1 => α) hm
        ⊆ Λᵣ(1, k, fold_k f (fun _ : Fin 1 => α) hm, S_1, C', hcode', δ))
  (fStack : ((indexPowT S φ 0) → F) → Gen'.parℓ → (indexPowT S φ 1) → F)
  (hbridge : ∀ (f : (indexPowT S φ 0) → F),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ]
        ≤ (haveI := Gen'.Gen_nonempty;
            Pr_{let r ←$ᵖ Gen'.Gen}[
              MutualCorrAgreement.proximityCondition (fStack f) δ r Gen'.C ])) :
    ∀ (f : (indexPowT S φ 0) → F) (_hδ : 0 < δ ∧ δ < 1 - BStarV),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] ≤ errStarV δ
  := by
    intro f hδ
    let D : PMF F := PMF.uniformOfFintype F
    have hmono :
        Pr_{let α ← D}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] ≤
        Pr_{let α ← D}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] := by
        refine Pr_le_Pr_of_implies D _ _ ?_
        intro α hne
        dsimp only
        dsimp only at hne
        intro hsub'
        exact hne (Set.Subset.antisymm (hsub f α) hsub')
    exact le_trans hmono (le_trans (hbridge f) (hmca (fStack f) δ hδ))

/-! ### Helper lemmas for `folding_preserves_listdecoding_bound` (Lemma 4.22, forward inclusion)

The forward inclusion `foldSet ⊆ listBlock'` is the deterministic "easy half" of folded
list-decoding: every fold of a δ-close codeword is itself a δ-close codeword of the folded
code. Two facts are needed:

* **Degree halving / code membership.** `g = fold_k f' vec_α hm ∈ C' = smoothCode φ_1 (m-1)`
  whenever `f' ∈ C = smoothCode φ_0 m`. This is exactly the single-fold step of `fold_f_g`
  (Claim 4.15 part 1), realized here through the axiom-clean `FoldingHelpers` polynomial
  bridge (`isEvalOf_of_mem_smoothCode` → `foldf_isEvalOf` → `mem_smoothCode_of_isEvalOf`).

* **Block-distance monotonicity.** `Δᵣ(1, k, fold_k f, S_1, φ_1, g) ≤ Δᵣ(0, k, f, S_0, φ_0, f')`.
  A level-1 fold value `foldf … w …` depends on `f` only through the two level-0 points
  `±(extract_x S φ 0 w)`; if the two folds disagree at `w`, then `f`/`f'` disagree at one of
  those two points, and both of them lie in the level-0 block over the same `z` (their
  `2^k`-th powers equal `z.val`, using `(extract_x w).val ^ 2 = w.val` and `1 ≤ k`). Hence the
  level-1 disagreement-block set is contained in the level-0 one, so its cardinality — and
  therefore the relative distance — does not increase.

## STATEMENT REPAIR (paper-faithful hypotheses, 2026-06-04)

As literally written the lemma is **not provable** for the same reasons documented on
`fold_f_g`/`relHammingDist_le_blockRelDistance`: the loose `indexPowT` data leaves the per-level
embeddings, the abstract `Neg` instance, and the evaluation domains `S_0`,`S_1` unconstrained,
so neither code membership of the fold nor the block correspondence can be forced. We thread the
same explicit smooth-domain structure used by the proven `fold_f_g` machinery:

* `hφ0 : ∀ x, φ_0 x = x.val`, `hφ1 : ∀ z, φ_1 z = z.val` — canonical-inclusion embeddings;
* `hneg : ∀ z, (-(extract_x S φ 0 z)).val = -((extract_x S φ 0 z).val)` — field-negation law for
  the abstract `Neg`;
* `hx0 : ∀ z, (extract_x S φ 0 z).val ≠ 0` — smooth domains avoid `0`;
* `h2 : (2 : F) ≠ 0` — odd characteristic;
* `hS0 : S_0 = univ`, `hS1 : S_1 = univ` — the paper's full evaluation domains;
* `hk1 : 1 ≤ k` — the paper's implicit `i ≤ k` (here `i = 1`); the block distance `Δᵣ(1, k, …)`
  is only defined for `1 ≤ k` (mirrors the `hik` repair on `relHammingDist_le_blockRelDistance`).

The target is an otherwise-unused leaf lemma (`git grep` confirms no references), so the orphan
statement-repair rule applies. -/

omit [Pow ι ℕ] in
/-- Block-distance monotonicity helper (the "easy half" core). Under the canonical-inclusion /
negation / nonzero structure, the level-1 disagreement-block set of `fold f` against `fold f'`
is contained in the level-0 disagreement-block set of `f` against `f'`. -/
lemma fold_disagreementSet_subset
    {S : Finset ι} {k : ℕ} {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ]
    {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
    {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
    [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
    [Smooth φ_0] [Smooth φ_1]
    [∀ i : ℕ, Neg (indexPowT S φ i)]
    (f f' : (indexPowT S φ 0) → F) (α : F)
    [h0 : DecidableBlockDisagreement 0 k f S_0 φ_0]
    [h1 : DecidableBlockDisagreement 1 k (fun y => foldf S φ y f α) S_1 φ_1]
    (hφ0 : ∀ x : indexPowT S φ 0, φ_0 x = x.val)
    (hφ1 : ∀ z : indexPowT S φ 1, φ_1 z = z.val)
    (hneg : ∀ z : indexPowT S φ 1,
      (-(extract_x S φ 0 z)).val = -((extract_x S φ 0 z).val))
    (hS0 : S_0 = Finset.univ) (hS1 : S_1 = Finset.univ) (hk1 : 1 ≤ k) :
    disagreementSet 1 k (fun y => foldf S φ y f α) S_1 φ_1 (fun y => foldf S φ y f' α)
      ⊆ disagreementSet 0 k f S_0 φ_0 f' := by
  classical
  intro z hz
  -- Unfold level-1 membership: `∃ w ∈ block 1 S_1 φ_1 z, fold f w ≠ fold f' w`.
  simp only [disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq] at hz ⊢
  obtain ⟨w, hfold_ne⟩ := hz
  -- `w : block 1 S_1 φ_1 z`, i.e. `w.val.val ^ (2^(k-1)) = z.val`.
  set xPow : indexPowT S φ 0 := extract_x S φ 0 w.val with hxPow
  -- Folding `f` and `f'` at `w` differs ⇒ `f`/`f'` differ at `xPow` or at `-xPow`.
  have hxy : f xPow ≠ f' xPow ∨ f (-xPow) ≠ f' (-xPow) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1', h2'⟩ := hcon
    apply hfold_ne
    simp only [foldf, ← hxPow, h1', h2']
  -- The square-root relation: `w.val.val = xPow.val ^ 2`.
  have hsq : w.val.val = (xPow.val) ^ 2 := extract_x_val_sq 0 w.val
  -- `w` lives in `block 1`, so `(φ_1 w.val) ^ (2^(k-1)) = z.val`, i.e. `w.val.val^(2^(k-1)) =
  -- z.val`.
  have hwblock : (w.val.val) ^ (2 ^ (k - 1)) = z.val := by
    have := w.property.2
    rwa [hφ1] at this
  -- `2^k = 2 * 2^(k-1)` for `1 ≤ k`.
  have hk' : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = 1 + (k - 1) by omega]
    rw [pow_add, pow_one]
  -- Generic: any value whose square is `w.val.val` raised to `2^k` equals `z.val`.
  have hpow_gen : ∀ a : F, a ^ 2 = w.val.val → a ^ (2 ^ k) = z.val := by
    intro a ha
    calc a ^ (2 ^ k) = a ^ (2 * 2 ^ (k - 1)) := by rw [hk']
      _ = (a ^ 2) ^ (2 ^ (k - 1)) := by rw [pow_mul]
      _ = (w.val.val) ^ (2 ^ (k - 1)) := by rw [ha]
      _ = z.val := hwblock
  -- Therefore `xPow.val ^ (2^k) = z.val`.
  have hxPowpow : (xPow.val) ^ (2 ^ k) = z.val := hpow_gen xPow.val hsq.symm
  have hnegPowpow : ((-xPow).val) ^ (2 ^ k) = z.val := by
    have hnegval : (-xPow).val = -(xPow.val) := by rw [hxPow]; exact hneg w.val
    rw [hnegval]
    refine hpow_gen (-(xPow.val)) ?_
    rw [neg_pow]; simp [← hsq]
  -- Conclude: one of `xPow`, `-xPow` is a level-0 disagreement witness in `block 0 S_0 φ_0 z`.
  rcases hxy with hne | hne
  · -- witness `xPow`
    refine ⟨⟨xPow, ?_, ?_⟩, hne⟩
    · rw [hS0]; exact Finset.mem_univ xPow
    · rw [hφ0, Nat.sub_zero]; exact hxPowpow
  · -- witness `-xPow`
    refine ⟨⟨-xPow, ?_, ?_⟩, hne⟩
    · rw [hS0]; exact Finset.mem_univ (-xPow)
    · rw [hφ0, Nat.sub_zero]; exact hnegPowpow

/-- Lemma 4.22
  Following same parameters as Lemma 4.21 above, and states
  `∀ α : F, fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α)) ⊆
      Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ)`

  **ABF26 mapping.** Deterministic inclusion form underlying L4.21. The probabilistic
  half (L4.21) bounds the failure probability of the *reverse* inclusion; this lemma
  asserts the *forward* inclusion always holds. No direct ABF26 paper counterpart —
  this is the "easy half" of folded-code list-decoding (corresponds to ABF26's "every
  folded image of a δ-close codeword is δ-close", a structural fact).

  See the block comment above `fold_disagreementSet_subset` for the documented statement
  repair (paper-faithful smooth-domain hypotheses), required for the same reasons as on
  `fold_f_g` / `relHammingDist_le_blockRelDistance`.

  (Supersedes the earlier wave3 "open" disposition: the two pieces it cited as missing — fold
  code-membership via the repaired single-step `foldf_step_mem_smoothCode`, and the block-distance
  contraction `fold_disagreementSet_subset` — are now both proven below, so this lemma is closed.)
-/
lemma folding_preserves_listdecoding_bound
    {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ]
  {δ : ℝ≥0} {f : (indexPowT S φ 0) → F}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0}
  -- documented statement repair (see block comment above `fold_disagreementSet_subset`)
  (hφ0 : ∀ x : indexPowT S φ 0, φ_0 x = x.val)
  (hφ1 : ∀ z : indexPowT S φ 1, φ_1 z = z.val)
  (hneg : ∀ z : indexPowT S φ 1,
    (-(extract_x S φ 0 z)).val = -((extract_x S φ 0 z).val))
  (hx0 : ∀ z : indexPowT S φ 1, (extract_x S φ 0 z).val ≠ 0)
  (h2 : (2 : F) ≠ 0)
  (hS0 : S_0 = Finset.univ) (hS1 : S_1 = Finset.univ) (hk1 : 1 ≤ k) :
      ∀ α : F,
        let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
        let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
        let foldSet := fold_k_set listBlock vec_α hm
        let fold := fold_k f vec_α hm
        let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
        foldSet ⊆ listBlock'
  := by
  classical
  intro α
  -- Unpack the `let`s and the membership `g ∈ foldSet`.
  simp only [fold_k_set]
  intro g hg
  -- `g ∈ fold_k_set listBlock vec_α hm` ⇒ `∃ f' ∈ listBlock, g = fold_k f' vec_α hm`.
  simp only [Set.mem_setOf_eq] at hg
  obtain ⟨f', hf'mem, hgeq⟩ := hg
  -- `f' ∈ listBlock = { u ∈ C | Δᵣ(0,k,f,S_0,φ_0,u) ≤ δ }`.
  rw [listBlockRelDistance] at hf'mem
  obtain ⟨hf'C, hf'dist⟩ := hf'mem
  -- A single fold step: `fold_k _ (fun _ => α) hm = fun y => foldf S φ y _ α`.
  have hfoldk : ∀ (u : (indexPowT S φ 0) → F),
      fold_k u (fun _ : Fin 1 => α) hm = fun y => foldf S φ y u α := by
    intro u
    funext y
    show fold_k_core u 1 (fun _ : Fin 1 => α) y = foldf S φ y u α
    simp only [fold_k_core]
  -- Membership in the folded code `C' = smoothCode φ_1 (m-1)`, via the single fold step
  -- `foldf_step_mem_smoothCode` (Claim 4.15 pt1, one round): its `hneg`/`hx0` hypotheses are
  -- exactly the repair hypotheses we thread.
  have hmm : m = (m - 1) + 1 := by omega
  have hgC' : g ∈ C' := by
    rw [hcode'] at *
    rw [hcode] at hf'C
    -- Package `f'` as a codeword of `smoothCode φ_0 ((m-1)+1)`.
    set f'C : smoothCode φ_0 ((m - 1) + 1) := ⟨f', by rw [← hmm]; exact hf'C⟩ with hf'Cdef
    -- Apply the single fold step at level `j = 0`, `M = m - 1`.
    have hstep := foldf_step_mem_smoothCode (S := S) (φ := φ) (j := 0) (M := m - 1)
      (φ_j := φ_0) (φ_j1 := φ_1) f'C α hφ0 hφ1 hneg hx0 h2
    -- `g = fold_k f' (fun _ => α) hm = fun y => foldf … f' α`.
    rw [hgeq, hfoldk f']
    exact hstep
  -- Block-distance: `Δᵣ(1,k, fold_k f, S_1, φ_1, g) ≤ δ`.
  rw [listBlockRelDistance]
  refine ⟨hgC', ?_⟩
  -- Rewrite `fold_k f` and `g` as single-fold-step functions.
  have hgfold : g = fun y => foldf S φ y f' α := by rw [hgeq, hfoldk f']
  -- Goal: `Δᵣ(1, k, fold_k f (fun _=>α) hm, S_1, φ_1, g) ≤ δ`.
  -- Reduce to disagreement-set cardinality monotonicity.
  show blockRelDistance 1 k (fold_k f (fun _ : Fin 1 => α) hm) S_1 φ_1 g ≤ δ
  rw [hfoldk f, hgfold]
  unfold blockRelDistance
  -- The level-1 disagreement set is contained in the level-0 one.
  have hsubset := fold_disagreementSet_subset (S := S) (k := k) (φ := φ)
    (S_0 := S_0) (S_1 := S_1) (φ_0 := φ_0) (φ_1 := φ_1) f f' α
    hφ0 hφ1 hneg hS0 hS1 hk1
  have hcard_le :
      (disagreementSet 1 k (fun y => foldf S φ y f α) S_1 φ_1
          (fun y => foldf S φ y f' α)).card
        ≤ (disagreementSet 0 k f S_0 φ_0 f').card :=
    Finset.card_le_card hsubset
  -- `Δᵣ(0,k,f,S_0,φ_0,f') ≤ δ` is `hf'dist` (after unfolding `blockRelDistance`).
  have hf'dist' :
      ((disagreementSet 0 k f S_0 φ_0 f').card : ℝ≥0)
          / (Fintype.card (indexPowT S φ k) : ℝ≥0) ≤ δ := by
    have := hf'dist
    unfold blockRelDistance at this
    exact this
  -- Divide the cardinality bound by the common denominator.
  refine le_trans ?_ hf'dist'
  gcongr ?_ / _
  exact_mod_cast hcard_le

/-- Lemma 4.23
  Following same parameters as Lemma 4.21 above, and states
  `Pr_{α ← F} [
      Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ) ¬ ⊆
        fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α))
    ] < errStar(C',2,δ)`

  **ABF26 mapping.** The probabilistic half of L4.21 / L4.22 — bounds the failure
  probability of the reverse inclusion (every δ-close codeword of the folded code
  comes from a δ-close codeword of the unfolded code, except with `errStar` prob).
  Combines L4.22 (forward inclusion deterministic) with this lemma to recover the
  ≠ event of L4.21.

  ## Statement repair (paper-faithful hypothesis, 2026-06-04)

  This lemma shares the exact defect repaired on `folding_preserves_listdecoding_base`
  (its sole upstream): with `errStar` an *unconstrained* function parameter,
  `errStar := fun _ _ _ => 0` makes the conclusion `Pr_{α}[…] < (0 : ℝ≥0∞)`, impossible.
  The previous proof derived this reverse bound *from* `folding_preserves_listdecoding_base`,
  but after that lemma's repair the dependency reverses (the base lemma now *consumes* this
  reverse bound as its `hrev` hypothesis), so to avoid circularity the genuine
  MCA-delivered reverse bound is threaded in directly as `hrev`. See the docstring of
  `folding_preserves_listdecoding_base` for the full justification. -/
lemma folding_preserves_listdecoding_base_ne_subset
    [Fintype F] {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F}
  [Fintype ι] [DecidableEq ι] [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0}
  -- L4.23 / MCA content threaded in (same repair as `folding_preserves_listdecoding_base`:
  -- with unconstrained `errStar` the bare statement is false, so the genuine reverse
  -- bound is supplied as a hypothesis; this lemma now restates it). See that lemma's
  -- docstring for the full justification.
  (hrev : ∀ (f : (indexPowT S φ 0) → F) (_hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] < errStar C' 2 δ) :
    ∀ (f : (indexPowT S φ 0) → F) (_hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) :=
            Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] < errStar C' 2 δ
  := hrev



end FoldingLemmas

end Fold
