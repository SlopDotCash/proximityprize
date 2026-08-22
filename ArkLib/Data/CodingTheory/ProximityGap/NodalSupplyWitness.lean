/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentSupplyIdentity

/-!
# The nodal-cubic supply witness (#389): the `m = 0` slice is EXACTLY solved

The split-nodal cubic kills every field-size condition at the `t = k+1` slice.
For `γ ≠ 0` the word

  `w(x) = x² + γ·x⁻¹`   (the graph of the nodal cubic `x·y = x³ + γ`)

has codeword agreements `≤ 3` (`nodal_word_agreement_le` — the plain root bound,
so `w` is in every capped class), and a `3`-subset `T` of the domain is an
explainable core as soon as `∏_{x∈T} x = −γ` (`nodal_explainableOn`): the
collinearity law of the nodal cubic is PURELY multiplicative — Vieta pins
`e₃ = −γ` while `e₁, e₂` are exactly the two degrees of freedom of a line.  On a
multiplicative subgroup the third point `−γ/(x₁x₂)` of every pair lies in the
domain automatically, so `≈ C(n,2)/3` cores fire — **independently of `q`**.

Probe (companion run to `probe_monomial_supply_witness.py`, exact):
`2,794,155` explainable `3`-cores on `μ₄₀₉₆ ⊂ F₁₂₂₈₉` vs the ceiling
`C(4096,2)/3 = 2,795,520` — the sandwich closes to `O(n)`, and the construction
is verbatim the same at `q = 2^128`.

The matching ceiling is `cap3_supply_mul_le`: for ANY word with agreements `≤ 3`,
the `3`-core count satisfies `3·E ≤ C(n,2)` — straight from the moment–supply
identity (`moment_identity_base`: `Σ_c C(a_c, 2) = C(n,2)` identically).
Together: **the `(k, m) = (2, 0)` agreement-capped supply is `C(n,2)/3 + O(n)`
EXACTLY, on every multiplicative-subgroup domain at EVERY field size** — the
first exact sub-Johnson supply value, and the refutation of every `B = o(n²)`
form of `SubJohnsonSupplyResidual` at `m = 0`: no `q`-condition can save it (the
nodal collinearity never references the additive structure that the Frobenius
witness needed, nor the field-size room the monomial witness needed).
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.NodalSupply

open ProximityGap.SpikeFloor ProximityGap.Ownership ProximityGap
open ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The nodal-cubic word `x ↦ x² + γ·x⁻¹` over the evaluation domain. -/
def nodalWord (dom : Fin n ↪ F) (γ : F) : Fin n → F :=
  fun i => dom i ^ 2 + γ * (dom i)⁻¹

/-- **The cap, for free**: every codeword agrees with the nodal word on at most
`3` points — agreements are roots of the cubic `X³ + γ − P·X`. -/
theorem nodal_word_agreement_le (dom : Fin n ↪ F) {γ : F}
    (h0 : ∀ i, dom i ≠ 0) (c : Fin n → F)
    (hc : c ∈ (rsCode dom 2 : Submodule F (Fin n → F))) :
    (agreeSet c (nodalWord dom γ)).card ≤ 3 := by
  obtain ⟨P, hPdeg, rfl⟩ := hc
  by_contra hgt
  push_neg at hgt
  set Q : F[X] := X ^ 3 + (C γ - P * X) with hQ
  have hPnd : P.natDegree ≤ 1 := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
      omega
  have hQnd : Q.natDegree ≤ 3 := by
    rw [hQ]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [Polynomial.natDegree_X_pow]
    refine max_le le_rfl ?_
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_C]
    refine max_le (by norm_num) ?_
    calc (P * X).natDegree ≤ P.natDegree + X.natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 3 := by rw [Polynomial.natDegree_X]; omega
  have hroots : ((agreeSet (fun i => P.eval (dom i)) (nodalWord dom γ)).image
      (fun i => dom i)).card ≤ 3 := by
    have hPX3 : (P * X).coeff 3 = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      calc (P * X).natDegree ≤ P.natDegree + X.natDegree :=
            Polynomial.natDegree_mul_le
        _ < 3 := by rw [Polynomial.natDegree_X]; omega
    have hQne : Q ≠ 0 := by
      intro h0'
      have hcoeff : Q.coeff 3 = 1 := by
        simp [hQ, coeff_add, coeff_sub, coeff_X_pow, Polynomial.coeff_C, hPX3]
      rw [h0', Polynomial.coeff_zero] at hcoeff
      exact one_ne_zero hcoeff.symm
    have hsub : ∀ x ∈ (agreeSet (fun i => P.eval (dom i))
        (nodalWord dom γ)).image (fun i => dom i), Q.IsRoot x := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter] at hi
      have hag := hi.2
      rw [nodalWord] at hag
      have hx0 := h0 i
      have hag' : dom i ^ 3 + γ = P.eval (dom i) * dom i := by
        have h := congrArg (· * dom i) hag.symm
        simp only at h
        field_simp at h
        linear_combination h
      rw [IsRoot, hQ]
      simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
      linear_combination hag'
    calc ((agreeSet (fun i => P.eval (dom i)) (nodalWord dom γ)).image
          (fun i => dom i)).card
        ≤ Q.roots.toFinset.card := by
          refine Finset.card_le_card fun x hx => ?_
          rw [Multiset.mem_toFinset, mem_roots hQne]
          exact hsub x hx
      _ ≤ Multiset.card Q.roots := Q.roots.toFinset_card_le
      _ ≤ Q.natDegree := Polynomial.card_roots' Q
      _ ≤ 3 := hQnd
  rw [Finset.card_image_of_injective _ dom.injective] at hroots
  omega

/-- **The core mechanism**: any `3`-subset with point-product `−γ` is an
explainable core of the nodal word — Vieta hands over the fitting line
`y = e₁·x − e₂`. -/
theorem nodal_explainableOn (dom : Fin n ↪ F) {γ : F}
    (h0 : ∀ i, dom i ≠ 0) {T : Finset (Fin n)} (hT : T.card = 3)
    (hprod : ∏ i ∈ T, dom i = -γ) :
    ExplainableOn dom 2 (nodalWord dom γ) T := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT
  have hprod' : dom a * (dom b * dom c) = -γ := by
    rw [← hprod, Finset.prod_insert (by simp [hab, hac]),
      Finset.prod_insert (by simp [hbc]), Finset.prod_singleton]
  have key : ∀ x : F, x ≠ 0 → (x = dom a ∨ x = dom b ∨ x = dom c) →
      (C (dom a + dom b + dom c) * X
        + C (-(dom a * dom b + dom a * dom c + dom b * dom c))).eval x
        = x ^ 2 + γ * x⁻¹ := by
    intro x hx0 hcase
    have hγ : γ = -(dom a * (dom b * dom c)) := by
      rw [hprod']; ring
    simp only [eval_add, eval_mul, eval_C, eval_X]
    rw [hγ]
    field_simp
    rcases hcase with rfl | rfl | rfl <;> ring
  refine ⟨fun i => (C (dom a + dom b + dom c) * X
      + C (-(dom a * dom b + dom a * dom c + dom b * dom c))).eval (dom i),
    ⟨_, lt_of_le_of_lt degree_linear_le ?_, rfl⟩, fun i hi => ?_⟩
  · exact_mod_cast Nat.one_lt_two
  · have hi3 : i = a ∨ i = b ∨ i = c := by
      rcases Finset.mem_insert.mp hi with h | h'
      · exact Or.inl h
      · rcases Finset.mem_insert.mp h' with h | h''
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Finset.mem_singleton.mp h''))
    have hmem : dom i = dom a ∨ dom i = dom b ∨ dom i = dom c := by
      rcases hi3 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rw [nodalWord]
    exact key (dom i) (h0 i) hmem

open Classical in
/-- **The supply floor of the nodal word**: every product-`(−γ)` triple is an
explainable core.  On a multiplicative subgroup every pair extends, so the count
is `C(n,2)/3 − O(n)` — at every field size. -/
theorem nodal_supply_ge (dom : Fin n ↪ F) {γ : F} (h0 : ∀ i, dom i ≠ 0) :
    ((((Finset.univ : Finset (Fin n)).powersetCard 3).filter
      (fun T => ∏ i ∈ T, dom i = -γ)).card)
      ≤ (degenerateSets dom 2 3 (nodalWord dom γ)).card := by
  refine Finset.card_le_card fun T hT => ?_
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
  rw [mem_degenerateSets]
  exact ⟨hT.1.2, nodal_explainableOn dom h0 hT.1.2 hT.2⟩

open Classical in
/-- **The exact ceiling at the cap-3 slice**: any word with all codeword
agreements `≤ 3` has at most `C(n,2)/3` explainable `3`-cores — the moment–supply
identity freezes the pair moment at `C(n,2)`, and each `3`-core spends three
pairs exclusively. -/
theorem cap3_supply_mul_le (dom : Fin n ↪ F) {w : Fin n → F}
    (hcap : ∀ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)),
      (agreeSet c w).card ≤ 3) :
    (degenerateSets dom 2 3 w).card * 3 ≤ n.choose 2 := by
  have hid := moment_supply_identity dom (by omega : 2 ≤ 3) w
  have hbase := moment_identity_base dom 2 w
  have hpt : ∀ c ∈ codewordFinset dom 2,
      ((agreeSet c w).card.choose 3) * 3 ≤ ((agreeSet c w).card.choose 2) := by
    intro c hc
    have h3 := hcap c (mem_codewordFinset.mp hc)
    interval_cases h : (agreeSet c w).card <;> decide
  calc (degenerateSets dom 2 3 w).card * 3
      = (∑ c ∈ codewordFinset dom 2, ((agreeSet c w).card.choose 3)) * 3 := by
        rw [hid]
    _ = ∑ c ∈ codewordFinset dom 2, ((agreeSet c w).card.choose 3) * 3 := by
        rw [Finset.sum_mul]
    _ ≤ ∑ c ∈ codewordFinset dom 2, ((agreeSet c w).card.choose 2) :=
        Finset.sum_le_sum hpt
    _ = n.choose 2 := hbase

end ProximityGap.NodalSupply

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.NodalSupply.nodal_word_agreement_le
#print axioms ProximityGap.NodalSupply.nodal_explainableOn
#print axioms ProximityGap.NodalSupply.nodal_supply_ge
#print axioms ProximityGap.NodalSupply.cap3_supply_mul_le
