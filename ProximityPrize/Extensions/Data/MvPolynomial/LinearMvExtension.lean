/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.MvPolynomial.LinearMvExtension

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Mirco Richter (Least Authority), Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ProximityPrize.Extensions.Data.CodingTheory.Basic.Distance
import ProximityPrize.Extensions.Data.CodingTheory.Basic.LinearCode
import ProximityPrize.Extensions.Data.CodingTheory.Basic.RelativeDistance
import ProximityPrize.Extensions.Data.MvPolynomial.Multilinear
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
  # Conversion of Univariate polynomials to Multilinear polynomials

  Univariate polynomials of degree < 2ᵐ can be writen as degree wise linear
  m-variate polynomials by `∑ aᵢ Xⁱ → ∑ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))` -/

namespace LinearMvExtension

noncomputable section

open MvPolynomial

variable {F : Type*} [CommSemiring F] {m : ℕ}

/-- The assignment realized by evaluating a `partialEval`'d polynomial at `β`: the first `k`
coordinates come from the substituted vector `α`, the remaining `m - k` from `β` (reindexed).
This is the explicit `Fin m → F` point that `partialEval_eval` collapses to. -/
def partialEvalAssignment {k : ℕ} (α : Fin k → F) (β : Fin (m - k) → F) (h : k ≤ m) :
    Fin m → F :=
  fun i => if h' : i.val < k then α ⟨i.val, h'⟩ else β ⟨i.val - k, by omega⟩

/-- Master evaluation lemma for `partialEval`: evaluating the partially-evaluated polynomial
at a residual point `β : Fin (m - k) → F` equals evaluating the original polynomial at the
combined assignment that uses `α` on the first `k` coordinates and `β` on the rest.

This is the workhorse that bridges `partialEval` to pointwise evaluation; every other
`partialEval` characterization in this file is derived from it. Proven by `eval_eval₂`:
`eval β (eval₂ C φ f) = eval₂ ((eval β).comp C) (fun i => eval β (φ i)) f`, where
`(eval β).comp C = RingHom.id` and `eval β (φ i)` is exactly the combined assignment. -/
lemma partialEval_eval {k : ℕ} (f : MvPolynomial (Fin m) F) (α : Fin k → F)
    (β : Fin (m - k) → F) (h : k ≤ m) :
    MvPolynomial.eval β (partialEval f α h)
      = MvPolynomial.eval (partialEvalAssignment α β h) f := by
  unfold partialEval
  rw [eval_eval₂]
  have hC : ((MvPolynomial.eval β).comp (C : F →+* MvPolynomial (Fin (m - k)) F))
      = RingHom.id F := by
    ext a; simp
  rw [hC, eval₂_id]
  have hfun : (fun s : Fin m => MvPolynomial.eval β
        (if h' : s.val < k then C (α ⟨s.val, h'⟩)
         else X (⟨s.val - k, by omega⟩ : Fin (m - k))))
      = partialEvalAssignment α β h := by
    funext i
    unfold partialEvalAssignment
    by_cases h' : i.val < k <;> simp [h']
  rw [hfun]

/-- `partialEval` at the empty challenge vector (`k = 0`) is the identity on evaluations:
since no variable is substituted, the residual assignment is `β` itself reindexed.
Here `partialEvalAssignment α β (h : 0 ≤ m)` reindexes `β : Fin (m - 0) → F` to `Fin m → F`. -/
lemma partialEval_eval_zero {f : MvPolynomial (Fin m) F} (α : Fin 0 → F)
    (β : Fin (m - 0) → F) (h : 0 ≤ m) :
    MvPolynomial.eval β (partialEval f α h)
      = MvPolynomial.eval (fun i : Fin m => β ⟨i.val, by omega⟩) f := by
  rw [partialEval_eval]
  have hfun : partialEvalAssignment α β h
      = (fun i : Fin m => β ⟨i.val, by omega⟩) := by
    funext i
    simp only [partialEvalAssignment, Nat.not_lt_zero, dif_neg, not_false_eq_true,
      Nat.sub_zero]
  rw [hfun]

private lemma binary_repr_sum (m i : ℕ) (hi : i < 2 ^ m) :
    ∑ j ∈ Finset.range m, (if Nat.testBit i j then 2 ^ j else 0) = i := by
  induction m generalizing i with
  | zero => simp_all
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.testBit_zero, pow_zero, decide_eq_true_eq]
    have key : ∑ x ∈ Finset.range m,
        (if i.testBit (x + 1) then 2 ^ (x + 1) else 0) =
      2 * ∑ x ∈ Finset.range m,
        (if (i / 2).testBit x then 2 ^ x else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp [Nat.testBit_add_one, pow_succ]
      ring_nf
    have hi2 : i / 2 < 2 ^ m := by rw [pow_succ] at hi; omega
    rw [key, ih (i / 2) hi2]
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h] <;> omega

/- Evaluating m-variate polynomials on (X^(2⁰), ... , X^(2ᵐ⁻¹) ) is
   right inverse to linear multivariate extensions on F^(< 2ᵐ)[X]  -/
/-- For `{0,1}`-valued `d : ℕ → ℕ`, the sum `∑ j ∈ range m, 2^j * d j` is `< 2^m`. -/
lemma sum_range_two_pow_lt (m : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j ≤ 1) :
    ∑ j ∈ Finset.range m, 2 ^ j * d j < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hdm := hd m
    nlinarith [Nat.zero_le (2 ^ m), pow_pos (show 0 < 2 by norm_num) m]

/-- The `ℓ`-th bit of `∑ j ∈ range m, 2^j * d_j` recovers `d ℓ` (for `{0,1}`-valued `d`,
`ℓ < m`). Binary-representation uniqueness, via `Nat.testBit_two_pow_mul_add`. -/
lemma testBit_sum_range_two_pow (m : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j ≤ 1) (ℓ : ℕ) (hℓ : ℓ < m) :
    (∑ j ∈ Finset.range m, 2 ^ j * d j).testBit ℓ = decide (d ℓ = 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hlow : (∑ j ∈ Finset.range m, 2 ^ j * d j) < 2 ^ m := sum_range_two_pow_lt m d hd
    have hcomm : (∑ j ∈ Finset.range m, 2 ^ j * d j) + 2 ^ m * d m
        = 2 ^ m * d m + (∑ j ∈ Finset.range m, 2 ^ j * d j) := by ring
    rw [hcomm, Nat.testBit_two_pow_mul_add (d m) hlow ℓ]
    by_cases hℓm : ℓ < m
    · rw [if_pos hℓm]; exact ih hℓm
    · have hℓe : ℓ = m := by omega
      rw [if_neg hℓm, hℓe, Nat.sub_self]
      have := hd m
      interval_cases (d m) <;> simp

/-- The encoding `d ↦ ∑ j, 2^j * d_j` is injective on `{0,1}`-valued `Fin m →₀ ℕ` — exactly the
support shape of a degreewise-linear polynomial. -/
lemma encode_inj_of_le_one (d e : Fin m →₀ ℕ)
    (hd : ∀ j, d j ≤ 1) (he : ∀ j, e j ≤ 1)
    (h : ∑ j : Fin m, 2 ^ (j : ℕ) * d j = ∑ j : Fin m, 2 ^ (j : ℕ) * e j) :
    d = e :=
  bitsValue_injOn hd he h

/-- The univariate monomial-sum form of `powAlgHom`.

Here `encode d = ∑ⱼ 2^j · dⱼ`. -/
lemma powAlgHom_eq_sum_support (q : MvPolynomial (Fin m) F) :
    powAlgHom q
      = ∑ d ∈ q.support,
          Polynomial.C (q.coeff d) * Polynomial.X ^ (∑ j : Fin m, 2 ^ (j : ℕ) * d j) := by
  unfold powAlgHom
  conv_lhs => rw [MvPolynomial.as_sum q, map_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod_pow]
  congr 1
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]

/-- The support of a degreewise-linear polynomial consists of `{0,1}`-valued exponent vectors. -/
lemma restrictDegree_support_le_one {q : MvPolynomial (Fin m) F}
    (hq : q ∈ MvPolynomial.restrictDegree (Fin m) F 1) :
    ∀ d ∈ q.support, ∀ j, d j ≤ 1 :=
  (MvPolynomial.mem_restrictDegree (σ := Fin m) (R := F) q 1).mp hq

/-- The univariate coefficient of `powAlgHom q` at the encoded degree of `d₀ ∈ support`
(`q` degreewise-linear) is exactly `q(d₀)`: the encoding injectivity rules out collisions. -/
lemma powAlgHom_coeff_encode_mem (q : MvPolynomial (Fin m) F)
    (hq : q ∈ MvPolynomial.restrictDegree (Fin m) F 1) (d₀ : Fin m →₀ ℕ) (hmem : d₀ ∈ q.support) :
    (powAlgHom q).coeff (∑ j : Fin m, 2 ^ (j : ℕ) * d₀ j) = q.coeff d₀ := by
  classical
  have hbound := restrictDegree_support_le_one hq
  rw [powAlgHom_eq_sum_support, Polynomial.finset_sum_coeff, Finset.sum_eq_single d₀]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro d hd hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have : (∑ j : Fin m, 2 ^ (j : ℕ) * d₀ j) ≠ (∑ j : Fin m, 2 ^ (j : ℕ) * d j) :=
      fun heq => hne (encode_inj_of_le_one d d₀ (hbound d hd) (hbound d₀ hmem) heq.symm)
    rw [if_neg this, mul_zero]
  · intro hcon; exact absurd hmem hcon

/-- **`powAlgHom` is injective on degreewise-linear polynomials** (trivial kernel). -/
lemma powAlgHom_eq_zero_of_restrictDegree (q : MvPolynomial (Fin m) F)
    (hq : q ∈ MvPolynomial.restrictDegree (Fin m) F 1) (h0 : powAlgHom q = 0) :
    q = 0 := by
  by_contra hne
  obtain ⟨d₀, hd₀⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hmem : d₀ ∈ q.support := by rwa [MvPolynomial.mem_support_iff]
  have hcoeff := powAlgHom_coeff_encode_mem q hq d₀ hmem
  rw [h0, Polynomial.coeff_zero] at hcoeff
  exact hd₀ hcoeff.symm

/-- `powAlgHom` of a degreewise-linear polynomial has degree `< 2^m`, hence lives in
`degreeLT F (2^m)` — the domain of `linearMvExtension`. -/
lemma powAlgHom_mem_degreeLT (q : MvPolynomial (Fin m) F)
    (hq : q ∈ MvPolynomial.restrictDegree (Fin m) F 1) :
    powAlgHom q ∈ Polynomial.degreeLT F (2 ^ m) := by
  rw [Polynomial.mem_degreeLT]
  have hnd : (powAlgHom q).natDegree ≤ 2 ^ m - 1 :=
    powAlgHom_of_restrict_degree_natDegree (p := ⟨q, hq⟩)
  have hlt : (powAlgHom q).natDegree < 2 ^ m :=
    lt_of_le_of_lt hnd (Nat.sub_lt ((by positivity : (0:ℕ) < 2 ^ m)) (by norm_num))
  by_cases h0 : powAlgHom q = 0
  · rw [h0, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by exact_mod_cast (WithBot.natCast_ne_bot (2 ^ m)))
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp hlt

/-- **Left inverse on degreewise-linear polynomials.** For `q ∈ restrictDegree (Fin m) F 1`,
re-extending its univariate `powAlgHom` image recovers `q`. Together with
`powAlgHom_is_right_inverse_to_linearMvExtension`, this makes `linearMvExtension` a bijection
between `degreeLT (2^m)` and the degreewise-linear `m`-variate polynomials. -/
lemma linearMvExtension_powAlgHom {F : Type*} [CommRing F] {m : ℕ} (q : MvPolynomial (Fin m) F)
    (hq : q ∈ MvPolynomial.restrictDegree (Fin m) F 1) :
    linearMvExtension ⟨powAlgHom q, powAlgHom_mem_degreeLT q hq⟩ = q := by
  set L := linearMvExtension (⟨powAlgHom q, powAlgHom_mem_degreeLT q hq⟩ :
      Polynomial.degreeLT F (2 ^ m)) with hL
  have hL_mem : L ∈ MvPolynomial.restrictDegree (Fin m) F 1 := by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    exact linearMvExtension_degreeOf_lt (p := ⟨powAlgHom q, powAlgHom_mem_degreeLT q hq⟩)
  have hpow : powAlgHom (L - q) = 0 := by
    have hr : powAlgHom L = powAlgHom q := by
      have := powAlgHom_is_right_inverse_to_linearMvExtension
        (⟨powAlgHom q, powAlgHom_mem_degreeLT q hq⟩ : Polynomial.degreeLT F (2 ^ m))
      simpa [hL] using this
    rw [map_sub, hr, sub_self]
  have hsub_mem : (L - q) ∈ MvPolynomial.restrictDegree (Fin m) F 1 :=
    Submodule.sub_mem _ hL_mem hq
  exact sub_eq_zero.mp (powAlgHom_eq_zero_of_restrictDegree (L - q) hsub_mem hpow)

/-- `partialEval` preserves degreewise-linearity: substituting constants for some variables and
single variables for the rest keeps the per-variable degree `≤ 1`. -/
lemma partialEval_mem_restrictDegree {F : Type*} [CommRing F] [Nontrivial F] {m k : ℕ}
    (f : MvPolynomial (Fin m) F) (hf : f ∈ MvPolynomial.restrictDegree (Fin m) F 1)
    (αs : Fin k → F) (hk : k ≤ m) :
    partialEval f αs hk ∈ MvPolynomial.restrictDegree (Fin (m - k)) F 1 := by
  classical
  rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
  intro i
  set φ : Fin m → MvPolynomial (Fin (m - k)) F := fun j =>
    if h' : j.val < k then MvPolynomial.C (αs ⟨j.val, h'⟩)
    else MvPolynomial.X (⟨j.val - k, by omega⟩ : Fin (m - k)) with hφ
  have hpe : partialEval f αs hk = eval₂ MvPolynomial.C φ f := rfl
  rw [hpe]
  conv_lhs => rw [MvPolynomial.as_sum f, MvPolynomial.eval₂_sum]
  refine le_trans (MvPolynomial.degreeOf_sum_le i _ _) (Finset.sup_le ?_)
  intro d hd
  rw [MvPolynomial.eval₂_monomial]
  refine le_trans (MvPolynomial.degreeOf_C_mul_le _ i _) ?_
  rw [Finsupp.prod]
  refine le_trans (MvPolynomial.degreeOf_prod_le i _ _) ?_
  have hdbound : ∀ j, d j ≤ 1 :=
    (MvPolynomial.mem_restrictDegree (σ := Fin m) (R := F) f 1).mp hf d hd
  have hterm : ∀ j ∈ d.support, MvPolynomial.degreeOf i ((φ j) ^ (d j))
      ≤ (if j = (⟨i.val + k, by omega⟩ : Fin m) then 1 else 0) := by
    intro j _
    refine le_trans (MvPolynomial.degreeOf_pow_le i _ _) ?_
    by_cases hjk : j.val < k
    · rw [hφ]; simp only [hjk, dif_pos]
      rw [MvPolynomial.degreeOf_C, mul_zero]
      positivity
    · rw [hφ]; simp only [hjk, dif_neg, not_false_eq_true]
      rw [MvPolynomial.degreeOf_X]
      by_cases hji : j = (⟨i.val + k, by omega⟩ : Fin m)
      · rw [if_pos hji]
        have hiv : i = (⟨j.val - k, by omega⟩ : Fin (m - k)) := by
          apply Fin.ext
          have : j.val = i.val + k := congrArg Fin.val hji
          simp only; omega
        rw [if_pos hiv, mul_one]
        exact hdbound j
      · rw [if_neg hji]
        have hne : ¬ (i = (⟨j.val - k, by omega⟩ : Fin (m - k))) := by
          intro h
          apply hji
          apply Fin.ext
          have hh : i.val = j.val - k := congrArg Fin.val h
          simp only; omega
        rw [if_neg hne, mul_zero]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_ite_eq' d.support (⟨i.val + k, by omega⟩ : Fin m) (fun _ => (1:ℕ))]
  split <;> simp

end

end LinearMvExtension
