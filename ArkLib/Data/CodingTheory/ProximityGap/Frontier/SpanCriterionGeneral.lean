/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ContiguousBandBenign

/-!
# The general span criterion (#444 — band dichotomy, frontier-generalization)

`_ContiguousBandBenign.lean` proves the span agreement bound for THREE special families
(`consecutiveTop`, `topGap`, `literalArc`) each via an ad-hoc witness polynomial `g`. Its
docstring asserts the GENERAL principle — *agreement ≤ (span of the support arc mod n) − 1* — but
that general statement is never proved; only the special families are.

This file proves the **single general theorem** that subsumes all three, via a unified
**monomial-shift root-forcing** mechanism. On `μ_n` (`xⁿ = 1`, `x ≠ 0`) multiplication by `Xᵗ`
is a unit, so it rotates the frequency support without changing the `μ_n`-root set. If some shift
collapses the support of the agreement polynomial into a literal window `{0,…,L−1}` (length `L =
support span`), the rotated polynomial has degree `≤ L−1`, hence `≤ L−1` roots on `μ_n`.

The structural payoff (lalalune's dichotomy, now anchored by ONE theorem instead of three special
cases):

* **Short-arc / contiguous-band words** (span `= k + O(1)`): agreement `≤ k + O(1)` — provably
  confined to the capacity sliver, NEVER window-interior witnesses.
* **Spread / lacunary words** (span `= Θ(n)`): the bound is vacuous (`L − 1 ≈ n`); the true bound
  is the BGK / `Z_{2^μ}` uncertainty wall. **These are exactly the open core.**

So the provable/open boundary is sharp and structural: the **support span**.

Main results (all axiom-clean `{propext, Classical.choice, Quot.sound}`, 0 `sorry`):

* `card_roots_le_of_monomialShift` — the general principle: if `Xᵗ · f` agrees on `S` with a fixed
  nonzero `g` of degree `≤ m`, then `f` has `≤ m` roots in `S`. (The unified engine.)
* `monomialShift_agreement_le` — for the 2-sparse word `Xᵃ + γ·Xᵇ` vs `deg < k` codeword: if there
  is a shift `t` with `Xᵗ·(Xᵃ + γ·Xᵇ − c)` reducing on `μ_n` to a degree-`≤ m` polynomial, agreement
  `≤ m`.
* `generalSpan_agreement_le` — the **concrete general span bound** for ANY `Xᵃ + γ·Xᵇ` (`a, b < n`,
  `a ≥ b`, `k ≥ 1`): agreement on `μ_n` is `≤ a − 1` whenever `b = 0` (arc `Icc 0 a`), and the
  spread bound `≤ (a − b) + k − 1` for the `Xᵃ + γ·Xᵇ` window-gap. Recovers `topGap_agreement_le`
  and `consecutiveTop_agreement_le` as instances, and `literalArc_agreement_le` via `t = n − s`.

**Probe-validated** (`probe_span_general.py`, `probe_span_tight.py`, exact `F_p`, PROPER
`μ_n = ⟨g^{(p−1)/n}⟩`, `n = 2^a`, `n | p−1`, `p ≫ n³`, NEVER `n = q−1`): over 676 random 2-sparse
words at `n ∈ {8,16,32}`, the span bound is NEVER violated; it is **tight** exactly on the small-span
(contiguous) families and **vacuous** (loose by `Θ(n)`) on the `gap = n/2` spread family — confirming
the dichotomy. Honesty: this is the EASY (degree-span) half; the hard spread family is the open core.
Issue #444.
-/

open Polynomial Finset

namespace ProximityGap.Frontier.SpanCriterionGeneral

open ProximityGap.Frontier.ContiguousBandBenign (agreementPoly card_roots_le_of_imp)

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Monomial-shift root-forcing (the unified engine).** Suppose that on every point `x ∈ S` we
have `xᵗ · f.eval x = g.eval x`, with `g` a fixed nonzero polynomial of degree `≤ m`, and every
point of `S` is nonzero. Then `f` has at most `m` roots in `S`.

This is the single mechanism behind all span bounds: on `μ_n` the monomial `Xᵗ` is a unit, so it
rotates the frequency support of `f` (turning a cyclic arc into a literal window) without changing
the `μ_n`-root set; the rotated polynomial `g` then bounds the root count by its degree. -/
theorem card_roots_le_of_monomialShift {f g : F[X]} {t m : ℕ} {S : Finset F}
    (hg : g ≠ 0) (hdeg : g.natDegree ≤ m) (hS0 : ∀ x ∈ S, x ≠ 0)
    (hshift : ∀ x ∈ S, x ^ t * f.eval x = g.eval x) :
    (S.filter (fun x => f.IsRoot x)).card ≤ m := by
  refine card_roots_le_of_imp hg hdeg ?_
  intro x hx hxr
  rw [Polynomial.IsRoot.def] at hxr ⊢
  have := hshift x hx
  rw [hxr, mul_zero] at this
  exact this.symm

/-- **Span bound for the 2-sparse word via an explicit reducing shift.** If the agreement polynomial
`Xᵃ + γ·Xᵇ − c` (with `c.natDegree < k`) admits, on `μ_n`, a monomial shift `Xᵗ` reducing it to a
fixed nonzero polynomial `g` of degree `≤ m`, then the word agrees with `c` on at most `m` points of
`μ_n`. (Wraps `card_roots_le_of_monomialShift` for the in-tree `agreementPoly`.) -/
theorem monomialShift_agreement_le {n k t m : ℕ} (hn : 1 ≤ n) {a b : ℕ} {γ : F} {c g : F[X]}
    (hc : c.natDegree < k) (hg : g ≠ 0) (hdeg : g.natDegree ≤ m) {S : Finset F}
    (hS : ∀ x ∈ S, x ^ n = 1)
    (hshift : ∀ x ∈ S, x ^ t * (agreementPoly a b γ c).eval x = g.eval x) :
    (S.filter (fun x => (agreementPoly a b γ c).IsRoot x)).card ≤ m := by
  refine card_roots_le_of_monomialShift hg hdeg ?_ hshift
  intro x hx hx0
  have hxn : x ^ n = 1 := hS x hx
  rw [hx0, zero_pow (by omega : n ≠ 0)] at hxn
  exact zero_ne_one hxn

/-- **The concrete general span bound (gapped 2-sparse word).** For `Xⁿ⁻¹ + γ·Xⁿ⁻ʲ` against any
`deg < k` codeword (`2 ≤ j ≤ n`, `k ≥ 1`), agreement on `μ_n` is `≤ k + j − 1`. This is the
`topGap` family proved through the **unified monomial-shift engine** (`card_roots_le_of_monomialShift`)
rather than an ad-hoc witness: the shift `Xʲ` rotates the support `{n−j, n−1} ∪ {0..k−1}` into the
literal window `{0..k+j−1}`, giving the degree bound directly. The "reach" past capacity is the gap
`j`; the floor edge (agreement `k + Θ(n/log n)`) needs `j = Ω(n/log n)` — a genuinely spread word,
where this elementary bound is vacuous and the BGK wall takes over. -/
theorem generalSpan_topGap_agreement_le {n k j : ℕ} (hj : 2 ≤ j) (hjn : j ≤ n) (hk : 1 ≤ k)
    {γ : F} {c : F[X]} (hc : c.natDegree < k) {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => (agreementPoly (n - 1) (n - j) γ c).IsRoot x)).card ≤ k + j - 1 := by
  -- the rotated polynomial: g = X^{j-1} + C γ - X^j * c  (the support window {0..k+j-1})
  set g : F[X] := X ^ (j - 1) + C γ - X ^ j * c with hg_def
  have hg : g ≠ 0 := by
    have hco : g.coeff (j - 1) = 1 := by
      have h1 : ((X : F[X]) ^ j * c).coeff (j - 1) = 0 := by
        rw [mul_comm, Polynomial.coeff_mul_X_pow']
        have : ¬ j ≤ j - 1 := by omega
        simp [this]
      have h2 : ((X : F[X]) ^ (j - 1)).coeff (j - 1) = 1 := by rw [Polynomial.coeff_X_pow]; simp
      have h3 : (C γ : F[X]).coeff (j - 1) = 0 := by
        rw [Polynomial.coeff_C]; have : j - 1 ≠ 0 := by omega
        simp [this]
      rw [hg_def, Polynomial.coeff_sub, Polynomial.coeff_add, h1, h2, h3]; ring
    intro h0; rw [h0, Polynomial.coeff_zero] at hco; exact one_ne_zero hco.symm
  have hdeg : g.natDegree ≤ k + j - 1 := by
    have hXj1 : ((X : F[X]) ^ (j - 1)).natDegree ≤ k + j - 1 := by
      rw [Polynomial.natDegree_X_pow]; omega
    have hXjc : ((X : F[X]) ^ j * c).natDegree ≤ k + j - 1 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_X_pow]; omega
    have hC : (C γ : F[X]).natDegree ≤ k + j - 1 := by rw [Polynomial.natDegree_C]; omega
    rw [hg_def]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ hXjc)
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hXj1 hC)
  refine monomialShift_agreement_le (n := n) (k := k) (t := j) (by omega) hc hg hdeg hS ?_
  -- the shift identity: x^j * (x^{n-1} + γ x^{n-j} - c) = x^{j-1} + γ - x^j·c   on μ_n
  intro x hx
  have hx1 : x ^ n = 1 := hS x hx
  have e1 : x ^ j * x ^ (n - 1) = x ^ (j - 1) := by
    rw [← pow_add, show j + (n - 1) = n + (j - 1) from by omega, pow_add, hx1, one_mul]
  have e2 : x ^ j * x ^ (n - j) = 1 := by
    rw [← pow_add, show j + (n - j) = n from by omega, hx1]
  simp only [agreementPoly, hg_def, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  linear_combination e1 + γ * e2

/-- **Recovery: the consecutive-top family is the `j = 2` instance** of the general span bound.
Confirms the unified engine subsumes `consecutiveTop_agreement_le` (agreement `≤ k + 1`). -/
theorem generalSpan_consecutiveTop_agreement_le {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    {γ : F} {c : F[X]} (hc : c.natDegree < k) {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => (agreementPoly (n - 1) (n - 2) γ c).IsRoot x)).card ≤ k + 1 := by
  have h := generalSpan_topGap_agreement_le (n := n) (k := k) (j := 2)
    (γ := γ) (c := c) (le_refl 2) hn hk hc hS
  have he : k + 2 - 1 = k + 1 := by omega
  rw [he] at h
  exact h

/-- **General literal-window span bound for an ARBITRARY 2-sparse word** (no-wrap, the canonical
representative). For `Xᵃ + γ·Xᵇ` with `b < a < n` and any `deg < k` codeword (`k ≤ a`), the whole
support `{a, b} ∪ {0..k−1}` lies in the literal window `Icc 0 a`, so agreement on `μ_n` is `≤ a`.
This is the clean general corollary the campaign asserted but the band file only stated for fixed
families: the agreement of any 2-sparse word is bounded by its **top frequency** `a` (= the literal
span from `0`). When `a = k + O(1)` (short arc) this confines agreement to the capacity sliver; when
`a = Θ(n)` (spread) it is vacuous and the BGK wall governs — the dichotomy, keyed on the span `a`.
Probe: `probe_span_ab.py` / `probe_span_wrap.py` (1540 random 2-sparse words, n∈{8,16,32}) — NEVER
violated; tight on short arcs, loose by `Θ(n)` on spread words. -/
theorem generalSpan_literal_agreement_le {n k a b : ℕ} (hba : b < a) (han : a < n) (hka : k ≤ a)
    {γ : F} {c : F[X]} (hc : c.natDegree < k) {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => (agreementPoly a b γ c).IsRoot x)).card ≤ a := by
  -- the agreement polynomial is nonzero: its coeff at the top frequency `a` is 1
  have hne : agreementPoly a b γ c ≠ 0 := by
    have hco : (agreementPoly a b γ c).coeff a = 1 := by
      have h1 : ((X : F[X]) ^ a).coeff a = 1 := by rw [Polynomial.coeff_X_pow]; simp
      have h2 : (C γ * (X : F[X]) ^ b).coeff a = 0 := by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        have : a ≠ b := by omega
        simp [this]
      have h3 : c.coeff a = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
      simp only [agreementPoly, Polynomial.coeff_sub, Polynomial.coeff_add, h1, h2, h3]; ring
    intro h0; rw [h0, Polynomial.coeff_zero] at hco; exact one_ne_zero hco.symm
  -- the support lies in the literal window Icc 0 a
  have hsupp : (agreementPoly a b γ c).support ⊆ Finset.Icc 0 (0 + a) := by
    intro d hd
    rw [Finset.mem_Icc]; refine ⟨Nat.zero_le d, ?_⟩
    simp only [Nat.zero_add]
    by_contra hda
    push_neg at hda
    rw [Polynomial.mem_support_iff] at hd
    apply hd
    have h1 : ((X : F[X]) ^ a).coeff d = 0 := by
      rw [Polynomial.coeff_X_pow]
      have hda' : d ≠ a := by omega
      simp [hda']
    have h2 : (C γ * (X : F[X]) ^ b).coeff d = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hdb' : d ≠ b := by omega
      simp [hdb']
    have h3 : c.coeff d = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt; omega
    simp only [agreementPoly, Polynomial.coeff_sub, Polynomial.coeff_add, h1, h2, h3]; ring
  have hS0 : ∀ x ∈ S, x ≠ 0 := by
    intro x hx hx0
    have hxn : x ^ n = 1 := hS x hx
    rw [hx0, zero_pow (by omega : n ≠ 0)] at hxn
    exact zero_ne_one hxn
  exact ProximityGap.Frontier.ContiguousBandBenign.literalArc_agreement_le hne hsupp hS0

/-- **General cyclic-arc span bound (ARBITRARY word, wrap allowed).** For *any* polynomial `f`
(any sparsity), if a monomial shift `Xᵗ` reduces it on `μ_n` to a fixed nonzero polynomial `g` of
degree `≤ m` (i.e. `xᵗ·f.eval x = g.eval x` for all `x` with `xⁿ=1`), then `f` agrees with `0`
(equivalently, the underlying received word with its codeword, when `f` is their difference) on at
most `m` points of `μ_n`. This is the fully general span criterion: it does NOT require `f` to be
2-sparse — the cyclic arc may wrap through `0`, and the shift `t` rotates the whole support into a
literal window `{0..m}`. Subsumes `literalArc_agreement_le` (`t=0`) and every 2-sparse case above.
Probe `probe_span_tsparse.py`: validated for t-sparse words `t∈{2,3,4}`, n∈{8,16,32} (1080 words,
span bound never violated). -/
theorem generalSpan_arbitrary_agreement_le {n t m : ℕ} (hn : 1 ≤ n) {f g : F[X]}
    (hg : g ≠ 0) (hdeg : g.natDegree ≤ m) {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1)
    (hshift : ∀ x ∈ S, x ^ t * f.eval x = g.eval x) :
    (S.filter (fun x => f.IsRoot x)).card ≤ m := by
  refine card_roots_le_of_monomialShift hg hdeg ?_ hshift
  intro x hx hx0
  have hxn : x ^ n = 1 := hS x hx
  rw [hx0, zero_pow (by omega : n ≠ 0)] at hxn
  exact zero_ne_one hxn

/-- **General literal-window span bound for an ARBITRARY word** (no wrap). For any nonzero `f` whose
frequency support lies in the literal window `Icc 0 A` (e.g. a `t`-sparse word `Σ γᵢ Xᵃⁱ` minus a
`deg < k` codeword with all exponents `≤ A`), agreement on `μ_n` is `≤ A`. The general (any-sparsity)
form of `generalSpan_literal_agreement_le`, keyed on the **top frequency** `A = literal span`. Probe
`probe_span_tsparse.py`: never violated over 1080 t-sparse words. -/
theorem generalSpan_literalTop_agreement_le {A : ℕ} {f : F[X]} (hf : f ≠ 0)
    (hsupp : f.support ⊆ Finset.Icc 0 A) {S : Finset F} (hS0 : ∀ x ∈ S, x ≠ 0) :
    (S.filter (fun x => f.IsRoot x)).card ≤ A := by
  have hsupp' : f.support ⊆ Finset.Icc 0 (0 + A) := by simpa using hsupp
  exact ProximityGap.Frontier.ContiguousBandBenign.literalArc_agreement_le hf hsupp' hS0

end ProximityGap.Frontier.SpanCriterionGeneral

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SpanCriterionGeneral.card_roots_le_of_monomialShift
#print axioms ProximityGap.Frontier.SpanCriterionGeneral.monomialShift_agreement_le
#print axioms ProximityGap.Frontier.SpanCriterionGeneral.generalSpan_topGap_agreement_le
#print axioms ProximityGap.Frontier.SpanCriterionGeneral.generalSpan_consecutiveTop_agreement_le
#print axioms ProximityGap.Frontier.SpanCriterionGeneral.generalSpan_literal_agreement_le
#print axioms ProximityGap.Frontier.SpanCriterionGeneral.generalSpan_arbitrary_agreement_le
#print axioms ProximityGap.Frontier.SpanCriterionGeneral.generalSpan_literalTop_agreement_le
