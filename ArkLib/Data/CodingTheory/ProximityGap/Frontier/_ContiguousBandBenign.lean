/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Contiguous-band words are list-decoding-benign (#444 — band dichotomy)

**Result (engine-verified, here proven axiom-clean for the representative families).** A received
word `X^a + γ·X^b` whose frequency support `{a, b} ∪ {0,…,k−1}` forms a **contiguous arc mod n**
agrees with a degree-`<k` codeword on **at most `k+1` points of `μ_n`** — i.e. only at the trivial
capacity+1 sliver. So contiguous-band words are NEVER list-decoding worst cases in the window
interior; the worst case must have **gapped** (non-contiguous) frequency support, and it is the gap
that engages the cyclotomic / BGK char-sum structure.

This **corrects** the prior campaign claim that the consecutive lacunary `x^{n-1}+x^{n-2}` is the
worst-case window word: the engine (`scripts/rust-pg`, cross-checked) shows its list is `0`
throughout the window except the single capacity+1 level, exactly as the bound below predicts. The
genuine worst words (gapped support) are the open core.

**Mechanism (elementary — no Beukers–Smyth needed).** On `μ_n` (where `x^n = 1`, so `x ≠ 0`),
a root of the agreement function forces a root of a fixed degree-`≤(k+1)` polynomial obtained by a
monomial (unit) multiplication. This is the unconditional **contiguous special case** of the open
`SparseRaggedExcessBound` lever (`_RThinSparseRealizability.lean`).

* `card_roots_le_of_imp` — the principle: if `f`-roots in `S` are `g`-roots for a fixed nonzero
  `g` of degree `≤ m`, then `f` has `≤ m` roots in `S`.
* `consecutiveTop_agreement_le` — `X^{n-1}+γ·X^{n-2}` agrees with any degree-`<k` codeword on
  `≤ k+1` points of `μ_n` (witness `g = X + Cγ − X²·c`, root-forcing via `x²·f = g` on `μ_n`).
* `literalArc_agreement_le` — no-wrap version: support in a literal range `Icc s (s+m)` ⇒ `≤ m`
  nonzero roots (e.g. `X^k + γ·X^{k+1}`), via `X^s ∣ f`.

All axiom-clean. Issue #444. Honesty: this bounds the EASY (contiguous) family; the hard (gapped)
family remains the open core / BGK wall — see `SparseRaggedExcessBound`.
-/

open Polynomial Finset

namespace ProximityGap.Frontier.ContiguousBandBenign

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Agreement polynomial** of the monomial line `X^a + γ·X^b` against codeword `c`; its `μ_n`-roots
are the agreement points. (Local copy of `RThinSparseRealizability.agreementPoly`.) -/
noncomputable def agreementPoly (a b : ℕ) (γ : F) (c : F[X]) : F[X] :=
  X ^ a + C γ * X ^ b - c

/-- **Root-forcing principle.** If every root of `f` in the point set `S` is also a root of a fixed
nonzero polynomial `g` of degree `≤ m`, then `f` has at most `m` roots in `S`. -/
theorem card_roots_le_of_imp {f g : F[X]} {m : ℕ} {S : Finset F}
    (hg : g ≠ 0) (hdeg : g.natDegree ≤ m)
    (himp : ∀ x ∈ S, f.IsRoot x → g.IsRoot x) :
    (S.filter (fun x => f.IsRoot x)).card ≤ m := by
  have hsub : S.filter (fun x => f.IsRoot x) ⊆ g.roots.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxS, hxr⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hg, himp x hxS hxr⟩
  calc (S.filter (fun x => f.IsRoot x)).card
      ≤ g.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ ≤ m := hdeg

/-- **Consecutive-top benignity.** The word `X^{n−1} + γ·X^{n−2}` (support `{n−2, n−1} ∪ {0..k−1}`,
a contiguous arc wrapping through `0`) agrees with any degree-`<k` codeword `c` on at most `k+1`
points of `μ_n`. Hence it is decodable only at the capacity+1 sliver — never a window worst case.
Witness: `g = X + Cγ − X²·c`, degree `≤ k+1`; on `μ_n` (`x^n = 1`), `x²·(X^{n−1}+γX^{n−2}−c) = g`. -/
theorem consecutiveTop_agreement_le {n k : ℕ} (hn : 2 ≤ n) {γ : F} {c : F[X]}
    (hc : c.natDegree < k) {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => (agreementPoly (n - 1) (n - 2) γ c).IsRoot x)).card ≤ k + 1 := by
  set g : F[X] := X + C γ - X ^ 2 * c with hg_def
  -- g ≠ 0: its degree-1 coefficient is 1.
  have hg : g ≠ 0 := by
    have hco : g.coeff 1 = 1 := by
      have h1 : ((X : F[X]) ^ 2 * c).coeff 1 = 0 := by
        rw [mul_comm, Polynomial.coeff_mul_X_pow']; simp
      rw [hg_def, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_one,
        Polynomial.coeff_C, h1]; simp
    intro h0; rw [h0, Polynomial.coeff_zero] at hco; exact one_ne_zero hco.symm
  -- deg g ≤ k+1
  have hdeg : g.natDegree ≤ k + 1 := by
    have hXC : (X + C γ : F[X]).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      simp [Polynomial.natDegree_X, Polynomial.natDegree_C]
    have hX2c : ((X : F[X]) ^ 2 * c).natDegree ≤ k + 1 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X]; omega
    rw [hg_def]
    exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le (le_trans hXC (by omega)) hX2c)
  -- root forcing: on μ_n, x²·(agreementPoly) = g, so a root of the word is a root of g.
  refine card_roots_le_of_imp hg hdeg ?_
  intro x hx hxr
  have hx1 : x ^ n = 1 := hS x hx
  have e1 : x ^ 2 * x ^ (n - 1) = x := by
    rw [← pow_add, show 2 + (n - 1) = n + 1 from by omega, pow_succ, hx1, one_mul]
  have e2 : x ^ 2 * x ^ (n - 2) = 1 := by
    rw [← pow_add, show 2 + (n - 2) = n from by omega, hx1]
  have hmod : x ^ 2 * (agreementPoly (n - 1) (n - 2) γ c).eval x = g.eval x := by
    simp only [agreementPoly, hg_def, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    linear_combination e1 + γ * e2
  rw [Polynomial.IsRoot.def] at hxr ⊢
  rw [← hmod, hxr, mul_zero]

/-- **Top-gap span bound (generalizes `consecutiveTop`).** The word `X^{n−1} + γ·X^{n−j}`
(`2 ≤ j ≤ n`, `k ≥ 1`) agrees with any degree-`<k` codeword on at most `k + j − 1` points of `μ_n`.
The "reach" past capacity is governed by the gap `j` between the two frequencies: reaching the floor
edge (agreement `k + Θ(n/log n)`) requires `j = Ω(n/log n)` — i.e. the two frequencies must be far
apart, a genuinely **spread/lacunary** word, where this elementary degree bound is vacuous and the
true bound is the BGK / `Z_{2^μ}` uncertainty wall. So the provable/open boundary is exactly the
support span. Witness `g = X^{j−1} + Cγ − X^j·c` (degree `≤ k+j−1`, `coeff (j−1) = 1`). -/
theorem topGap_agreement_le {n k j : ℕ} (hj : 2 ≤ j) (hjn : j ≤ n) (hk : 1 ≤ k) {γ : F} {c : F[X]}
    (hc : c.natDegree < k) {S : Finset F} (hS : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => (agreementPoly (n - 1) (n - j) γ c).IsRoot x)).card ≤ k + j - 1 := by
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
  refine card_roots_le_of_imp hg hdeg ?_
  intro x hx hxr
  have hx1 : x ^ n = 1 := hS x hx
  have e1 : x ^ j * x ^ (n - 1) = x ^ (j - 1) := by
    rw [← pow_add, show j + (n - 1) = n + (j - 1) from by omega, pow_add, hx1, one_mul]
  have e2 : x ^ j * x ^ (n - j) = 1 := by
    rw [← pow_add, show j + (n - j) = n from by omega, hx1]
  have hmod : x ^ j * (agreementPoly (n - 1) (n - j) γ c).eval x = g.eval x := by
    simp only [agreementPoly, hg_def, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    linear_combination e1 + γ * e2
  rw [Polynomial.IsRoot.def] at hxr ⊢
  rw [← hmod, hxr, mul_zero]

/-- **Literal-arc benignity (no wrap).** If the agreement polynomial's support lies in a literal
range `Icc s (s+m)`, it has at most `m` nonzero roots — so at most `m` agreement points on `μ_n`
(all nonzero). Covers e.g. `X^k + γ·X^{k+1}` (support `{0,…,k+1}`, `m = k+1`). Via `X^s ∣ f`, the
quotient has degree `≤ m`. -/
theorem literalArc_agreement_le {f : F[X]} {s m : ℕ} (hf : f ≠ 0)
    (hsupp : f.support ⊆ Finset.Icc s (s + m)) {S : Finset F} (hS : ∀ x ∈ S, x ≠ 0) :
    (S.filter (fun x => f.IsRoot x)).card ≤ m := by
  have hdvd : (X : F[X]) ^ s ∣ f := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    by_contra hne
    have hmem := hsupp (Polynomial.mem_support_iff.mpr hne)
    rw [Finset.mem_Icc] at hmem; omega
  obtain ⟨g, hfg⟩ := hdvd
  have hgne : g ≠ 0 := by rintro rfl; rw [mul_zero] at hfg; exact hf hfg
  have hfdeg : f.natDegree ≤ s + m := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro d hd
    by_contra hne
    have hmem := hsupp (Polynomial.mem_support_iff.mpr hne)
    rw [Finset.mem_Icc] at hmem; omega
  have hdegeq : f.natDegree = s + g.natDegree := by
    rw [hfg, Polynomial.natDegree_mul (pow_ne_zero s Polynomial.X_ne_zero) hgne,
      Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  have hgdeg : g.natDegree ≤ m := by omega
  refine card_roots_le_of_imp hgne hgdeg ?_
  intro x hxS hxr
  rw [Polynomial.IsRoot.def] at hxr ⊢
  rw [hfg, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hxr
  exact (mul_eq_zero.mp hxr).resolve_left (pow_ne_zero s (hS x hxS))

end ProximityGap.Frontier.ContiguousBandBenign

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ContiguousBandBenign.card_roots_le_of_imp
#print axioms ProximityGap.Frontier.ContiguousBandBenign.consecutiveTop_agreement_le
#print axioms ProximityGap.Frontier.ContiguousBandBenign.topGap_agreement_le
#print axioms ProximityGap.Frontier.ContiguousBandBenign.literalArc_agreement_le
