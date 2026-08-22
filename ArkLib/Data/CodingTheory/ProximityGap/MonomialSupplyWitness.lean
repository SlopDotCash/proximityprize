/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The monomial supply witness (#389): the generic-density phase is real

The mechanism behind the refutation of UNCONDITIONAL linear capped supply.  The
word `w = x^t` (`t = k+m+1`) is automatically in the capped class — its
codeword agreements are `≤ t ≤ 2k+m+1` (`monomial_word_agreement_le`, the plain
root bound) — and a `t`-subset `T` is an explainable core of `w` as soon as the
remainder `x^t mod ∏_{i∈T}(X − xᵢ)` has degree `< k`
(`explainableOn_of_remainder_degree_lt`): the remainder IS the fitting codeword.
The supply of the monomial word is therefore at least the number of `t`-subsets
whose remainder window vanishes (`monomial_supply_ge`) — a codimension-`(m+1)`
condition, of generic density `C(n,t)/q^{m+1}`.

**What the probes establish with this mechanism**
(`probe_far_subset_law.py` heuristics; the pair-hash count at the production
shape): on the FULL unit group of `F₁₂₇` the `x⁴` word has `630 = 5n` explainable
`4`-cores (agreement profile `{1: 5418, 2: 3969, 3: 42, 4: 630}` — capped at
`4 ≤ 6`); on THE standard 2-smooth domain `μ₄₀₉₆ ⊂ F₁₂₂₈₉` it has
`103,424 = 25.25·n` of them (subgroup-enhanced above the generic `19n`).  So:

* `SubJohnsonSupplyResidual` with `B = O(n)` is **FALSE without a `q ≫ n`
  hypothesis** — even over multiplicative subgroups, even over the campaign's own
  NTT domain.  The μ-immunity observed at `q ≫ n` is a field-size phenomenon
  (the generic density `C(n,t)/q^{m+1}` vanishes), not a multiplicative-structure
  one.
* The two-phase law is the corrected target:
  `E_max(μ_n) = Θ(n + C(n,t)/q^{m+1})` — arithmetic/fibre families rule the
  `q ≫ n` phase (where the prize lives, `q ≥ 2^128`), the generic density rules
  `n = Θ(q)`, and the unconditional pair-count ceiling `C(n,k)` is attained
  (up to the `t!`-constant) at `n ~ q`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.MonomialSupply

open ProximityGap.SpikeFloor ProximityGap.Ownership ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The monomial word `x ↦ x^t` over the evaluation domain. -/
def monomialWord (dom : Fin n ↪ F) (t : ℕ) : Fin n → F := fun i => dom i ^ t

/-- The node polynomial of a subset. -/
noncomputable def nodePoly (dom : Fin n ↪ F) (T : Finset (Fin n)) : F[X] :=
  ∏ i ∈ T, (X - C (dom i))

theorem nodePoly_monic (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (nodePoly dom T).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (dom i)

theorem nodePoly_eval_eq_zero (dom : Fin n ↪ F) {T : Finset (Fin n)}
    {i : Fin n} (hi : i ∈ T) : (nodePoly dom T).eval (dom i) = 0 := by
  rw [nodePoly, eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-- **The cap, for free**: every codeword agrees with the monomial word on at
most `t` points (`k ≤ t`) — the plain root bound.  In particular `x^{k+m+1}` is
in the agreement-capped class of `SubJohnsonSupplyResidual`. -/
theorem monomial_word_agreement_le (dom : Fin n ↪ F) {k t : ℕ}
    (hkt : k ≤ t) (c : Fin n → F)
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (agreeSet c (monomialWord dom t)).card ≤ t := by
  obtain ⟨P, hPdeg, rfl⟩ := hc
  by_contra hgt
  push_neg at hgt
  -- the difference X^t − P is nonzero of degree t with > t roots
  set Q : F[X] := X ^ t - P with hQ
  have hQdeg : Q.degree = t := by
    rw [hQ]
    have hXt : (X ^ t : F[X]).degree = t := by
      rw [degree_X_pow]
    rw [sub_eq_add_neg]
    rw [degree_add_eq_left_of_degree_lt]
    · exact hXt
    · rw [degree_neg, hXt]
      exact lt_of_lt_of_le hPdeg (by exact_mod_cast hkt)
  have hQne : Q ≠ 0 := by
    intro h0
    rw [h0, degree_zero] at hQdeg
    exact absurd hQdeg.symm (by simp)
  -- the agreement points are roots of Q
  have hroots : ((agreeSet (fun i => P.eval (dom i)) (monomialWord dom t)).image
      (fun i => dom i)).card ≤ t := by
    have hsub : ∀ x ∈ (agreeSet (fun i => P.eval (dom i))
        (monomialWord dom t)).image (fun i => dom i), Q.IsRoot x := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter] at hi
      have := hi.2
      rw [monomialWord] at this
      rw [IsRoot, hQ]
      simp only [eval_sub, eval_pow, eval_X]
      rw [← this]
      ring
    calc ((agreeSet (fun i => P.eval (dom i)) (monomialWord dom t)).image
          (fun i => dom i)).card
        ≤ Q.roots.toFinset.card := by
          refine Finset.card_le_card fun x hx => ?_
          rw [Multiset.mem_toFinset, mem_roots hQne]
          exact hsub x hx
      _ ≤ Multiset.card Q.roots := Q.roots.toFinset_card_le
      _ ≤ t := by
          have h := Polynomial.card_roots' Q
          rw [natDegree_eq_of_degree_eq_some hQdeg] at h
          exact h
  rw [Finset.card_image_of_injective _ dom.injective] at hroots
  omega

/-- **The core mechanism**: a `t`-subset whose remainder window vanishes — the
remainder of `x^t` by the node polynomial has degree `< k` — is an explainable
core of the monomial word: the remainder is the fitting codeword. -/
theorem explainableOn_of_remainder_degree_lt (dom : Fin n ↪ F) {k t : ℕ}
    {T : Finset (Fin n)}
    (hdeg : ((X ^ t : F[X]) %ₘ nodePoly dom T).degree < k) :
    ExplainableOn dom k (monomialWord dom t) T := by
  refine ⟨fun i => ((X ^ t : F[X]) %ₘ nodePoly dom T).eval (dom i),
    ⟨(X ^ t : F[X]) %ₘ nodePoly dom T, hdeg, rfl⟩, fun i hi => ?_⟩
  have hsplit := modByMonic_add_div (X ^ t : F[X]) (nodePoly dom T)
  have heval := congrArg (eval (dom i)) hsplit
  rw [monomialWord]
  simpa [eval_add, eval_mul, nodePoly_eval_eq_zero dom hi] using heval

open Classical in
/-- **The supply floor of the monomial word**: at least one explainable
`(k+m+1)`-core per vanishing remainder window — the generic-density family.
(Probe: `25.25·n` such cores at the production shape `μ₄₀₉₆ ⊂ F₁₂₂₈₉`.) -/
theorem monomial_supply_ge (dom : Fin n ↪ F) (k m : ℕ) :
    ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
      (fun T => ((X ^ (k + m + 1) : F[X]) %ₘ nodePoly dom T).degree < k)).card)
      ≤ ((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k (monomialWord dom (k + m + 1)) T)).card) := by
  refine Finset.card_le_card fun T hT => ?_
  rw [Finset.mem_filter] at hT ⊢
  exact ⟨hT.1, explainableOn_of_remainder_degree_lt dom hT.2⟩

end ProximityGap.MonomialSupply

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialSupply.monomial_word_agreement_le
#print axioms ProximityGap.MonomialSupply.explainableOn_of_remainder_degree_lt
#print axioms ProximityGap.MonomialSupply.monomial_supply_ge
