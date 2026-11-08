/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion

/-!
# The far-threshold maximality lemma (#407, B-count / B3): monomial agreement cap on `μ_n`

For a *smooth* evaluation domain — one with `(dom i)^n = 1` for every `i` (a `μ_n`-coset
in the FFT subgroup of the prize setting) — the monomial direction `x^b` has an
agreement ceiling (an upper bound, not shown to be attained) against the Reed–Solomon code:

> **`monomial_agreement_le_mod`** — every codeword of `rsCode dom k` (degree `< k`)
> agrees with the monomial word `w i = (dom i)^b` on at most `(b mod n)` points,
> provided `k ≤ (b mod n)`.

Mechanism (the degree-root bound): on `μ_n`, `(dom i)^b = (dom i)^(b mod n)` because
`(dom i)^n = 1`.  Agreement at `i` therefore means the polynomial `g = X^(b mod n) − P`
vanishes at `dom i`.  Since `deg P < k ≤ (b mod n)`, the leading term `X^(b mod n)`
survives the subtraction (`degree_sub_eq_left_of_degree_lt`), so `deg g = (b mod n)` and
`g ≠ 0`; the distinct points `dom i` of the agreement set are roots of `g`, hence number
at most `(b mod n)` (`card_roots'`).

**The far-direction corollary** (`monomial_FarFromCode_of_mod_lt`): on a smooth domain,
the monomial direction `x^b` is `FarFromCode` at radius `δ` (in the sense of
`FarCosetExplosion.FarFromCode`, no codeword agrees on a witness-sized set
`≥ (1−δ)·n`) whenever `(b mod n) < (1−δ)·n` — equivalently `(b mod n) < n − r` for the
"covering slack" `r = δ·n`.  This is a **sufficient** condition only: the low exponents with
`(b mod n) ∈ [k, ⌈(1−δ)n⌉)` are certified far, but the converse is false, because the degree
bound `b mod n` on the agreement need not be attained.  Counterexample: on the proper subgroup
`μ_8 ⊂ F_17` with `k = 1` (constant code) and `b = 3`, the map `x ↦ x^3` permutes `μ_8`
(`gcd(3, 8) = 1`), so `x^3` agrees with any constant on at most one point; at `δ = 3/4` the
witness threshold is `2`, so `x^3` is far although `b mod n = 3 ∉ [1, 2)` (its actual relative
distance to the code is `7/8`).  So this file does **not** show that only low exponents are far,
nor that the lowest far exponent `x^k` is the binding/extremal direction; any such
characterization needs a sharp agreement result, not just this upper bound.

This is count-lane support: it certifies some monomial directions as inputs to
`epsMCA_ge_far_incidence`.  Issue #407.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.FarThreshold

open ProximityGap.SpikeFloor ProximityGap.FarCosetExplosion

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **On a smooth domain, `(dom i)^b = (dom i)^(b mod n)`.**  The exponent of a monomial
word reduces modulo `n` because every domain value is an `n`-th root of unity. -/
theorem dom_pow_mod (dom : Fin n ↪ F) (hsmooth : ∀ i, (dom i) ^ n = 1) (b : ℕ) (i : Fin n) :
    (dom i) ^ b = (dom i) ^ (b % n) := by
  conv_lhs => rw [← Nat.div_add_mod b n]
  rw [pow_add, pow_mul, hsmooth i, one_pow, one_mul]

open Classical in
/-- **THE FAR-THRESHOLD MAXIMALITY LEMMA.**  On a smooth domain (`(dom i)^n = 1`), a
codeword of `rsCode dom k` agrees with the monomial word `x^b` on at most `(b mod n)`
points, whenever `k ≤ (b mod n)`.  (Degree-root bound: `X^(b mod n) − P` is a nonzero
polynomial of degree exactly `(b mod n)`, so it has at most `(b mod n)` roots — and every
agreement point is a root.) -/
theorem monomial_agreement_le_mod (dom : Fin n ↪ F) (hsmooth : ∀ i, (dom i) ^ n = 1)
    {k b : ℕ} (hkb : k ≤ b % n)
    {c : Fin n → F} (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => c i = (dom i) ^ b)).card ≤ b % n := by
  classical
  obtain ⟨P, hPdeg, rfl⟩ := hc
  set m := b % n with hm
  -- the obstruction polynomial g = X^m − P, of degree exactly m
  set g : F[X] := X ^ m - P with hg
  have hPdegm : P.degree < (m : WithBot ℕ) := by
    calc P.degree < (k : WithBot ℕ) := hPdeg
      _ ≤ (m : WithBot ℕ) := by exact_mod_cast hkb
  have hgdeg : g.degree = (m : WithBot ℕ) := by
    rw [hg, degree_sub_eq_left_of_degree_lt (by rw [degree_X_pow]; exact hPdegm),
      degree_X_pow]
  have hg0 : g ≠ 0 := by
    intro h; rw [h, degree_zero] at hgdeg; exact WithBot.bot_ne_coe hgdeg
  set A := (Finset.univ : Finset (Fin n)).filter
    (fun i => (fun i => P.eval (dom i)) i = (dom i) ^ b) with hA
  -- every agreement point gives a root of g
  have hroots : ∀ i ∈ A, g.IsRoot (dom i) := by
    intro i hi
    have hval : P.eval (dom i) = (dom i) ^ b := (Finset.mem_filter.mp hi).2
    have hmod : (dom i) ^ b = (dom i) ^ m := dom_pow_mod dom hsmooth b i
    simp only [IsRoot, hg, eval_sub, eval_pow, eval_X]
    rw [hval, hmod, sub_self]
  -- count: |A| ≤ #roots(g) ≤ deg g = m
  calc A.card
      = (A.image dom).card := (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ g.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp hx
        rw [Multiset.mem_toFinset, mem_roots hg0]
        exact hroots i hiA
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := card_roots' _
    _ = m := natDegree_eq_of_degree_eq_some hgdeg

open Classical in
/-- **The far-direction corollary.**  On a smooth domain, the monomial direction `x^b`
is `FarFromCode` (no codeword of `rsCode dom k` agrees on a witness-sized set
`≥ (1−δ)·n`) at radius `δ`, provided `k ≤ (b mod n)` and `(b mod n) < (1−δ)·n`.

This is a sufficient condition only: other monomial directions can also be far (e.g. on
`μ_8 ⊂ F_17` with `k = 1`, `δ = 3/4`, the direction `x^3` is far although `3 ∉ [1, 2)`),
so it does not identify all far directions or a binding/extremal exponent. -/
theorem monomial_FarFromCode_of_mod_lt (dom : Fin n ↪ F)
    (hsmooth : ∀ i, (dom i) ^ n = 1) {k b : ℕ} {δ : ℝ≥0}
    (hkb : k ≤ b % n) (hlt : (b % n : ℝ≥0) < (1 - δ) * (n : ℝ≥0)) :
    FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => (dom i) ^ b) := by
  intro c hc S hS
  by_contra hcon
  -- ¬ ∃ i ∈ S, c i ≠ x^b  ⟹  c agrees with x^b on all of S
  push_neg at hcon
  -- so S is contained in the agreement set, giving |S| ≤ b mod n
  have hSsub : S ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => c i = (dom i) ^ b) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon i hi⟩
  have hScard : S.card ≤ b % n :=
    le_trans (Finset.card_le_card hSsub) (monomial_agreement_le_mod dom hsmooth hkb hc)
  -- contradiction with the witness budget (1−δ)·n ≤ |S| but |S| ≤ b mod n < (1−δ)·n
  have hSge : (1 - δ) * (n : ℝ≥0) ≤ (S.card : ℝ≥0) := by
    have := hS; rwa [Fintype.card_fin] at this
  have hSle : (S.card : ℝ≥0) ≤ (b % n : ℝ≥0) := by exact_mod_cast hScard
  exact absurd (lt_of_le_of_lt (le_trans hSge hSle) hlt) (lt_irrefl _)

end ProximityGap.FarThreshold

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FarThreshold.dom_pow_mod
#print axioms ProximityGap.FarThreshold.monomial_agreement_le_mod
#print axioms ProximityGap.FarThreshold.monomial_FarFromCode_of_mod_lt
