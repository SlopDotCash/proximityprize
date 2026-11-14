/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# The sub-Johnson list bound ⟹ the supply (#389, the open-core wiring)

This file derives `ExplainableCoreSupply` from the all-word
`SubJohnsonListBound` hypothesis used in #389.

The named residual (`SubJohnsonListBound`): for every word `w`, the codewords of
`rsCode dom k` whose agreement with `w` is `≥ k+m+1` number at most `L`, and each
agrees on at most `A` points. Taking the received word to be the zero codeword forces
`n ≤ A` when `k+m+1 ≤ n`, independently of the evaluation domain.

The wiring theorem (`explainableCoreSupply_of_listBound`): every explainable
`(k+m+1)`-core has a *unique* explaining codeword (two degree-`<k` codewords
agreeing on `k+m+1 > k−1` points coincide), so the cores inject into
`(codeword, (k+m+1)-subset of its agreement set)` pairs:

  `#cores ≤ Σ_{c : agree ≥ k+m+1} C(agree(c,w), k+m+1) ≤ L · C(A, k+m+1)`.

The resulting budget `L·C(A,k+m+1)` is at least `C(n,k+m+1)`, by
`subJohnsonListBound_supply_budget`. Obtaining a smaller budget requires a
restriction on received words or a bound directly on coherent fibers.
Polynomial worst-case list bounds in the production sub-Johnson regime remain open.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset Polynomial

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The agreement set of a function `c` with `w`. -/
def listAgreeSet (c w : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i = w i)

open Classical in
/-- The codewords with agreement `≥ k+m+1` with `w` (the sub-Johnson list). -/
noncomputable def bigAgreeCodewords (dom : Fin n ↪ F) (k m : ℕ) (w : Fin n → F) :
    Finset (Fin n → F) :=
  (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ k + m + 1 ≤ (listAgreeSet c w).card)

open Classical in
/-- The all-word sub-Johnson list hypothesis. For every word `w`,
the codewords agreeing with `w` on `≥ k+m+1` points number `≤ L`, and each agrees
on `≤ A` points. See `subJohnsonListBound_agreement_cap` for the necessary lower bound on `A`. -/
def SubJohnsonListBound (dom : Fin n ↪ F) (k m L A : ℕ) : Prop :=
  ∀ w : Fin n → F,
    (bigAgreeCodewords dom k m w).card ≤ L
      ∧ ∀ c ∈ bigAgreeCodewords dom k m w, (listAgreeSet c w).card ≤ A

/-- Census-tracked alias of `SubJohnsonListBound`. The above-Johnson provider is
`SubJohnsonListDischarge.subJohnsonListBound_aboveJohnson`; the all-word
agreement cap is subject to `subJohnsonListBound_agreement_cap`. -/
def SubJohnsonListResidual (dom : Fin n ↪ F) (k m L A : ℕ) : Prop :=
  SubJohnsonListBound dom k m L A

/-- An all-word agreement cap must include full agreement with the zero codeword
whenever the agreement threshold is at most the block length. -/
theorem subJohnsonListBound_agreement_cap (dom : Fin n ↪ F) {k m L A : ℕ}
    (hthreshold : k + m + 1 ≤ n) (h : SubJohnsonListBound dom k m L A) :
    n ≤ A := by
  classical
  have hz : (0 : Fin n → F) ∈ bigAgreeCodewords dom k m 0 := by
    simp [bigAgreeCodewords, listAgreeSet]
    omega
  simpa [listAgreeSet] using (h 0).2 0 hz

open Classical in
/-- **Uniqueness of the explaining codeword.**  Two degree-`<k` codewords agreeing
with `w` on a `(k+m+1)`-core coincide (they agree on `k+m+1 > k−1` points). -/
theorem explainer_unique (dom : Fin n ↪ F) {k : ℕ} {w : Fin n → F}
    {T : Finset (Fin n)} (hk : 1 ≤ k) (hT : k ≤ T.card)
    {c c' : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hcag : ∀ i ∈ T, c i = w i) (hc'ag : ∀ i ∈ T, c' i = w i) :
    c = c' := by
  obtain ⟨P, hPdeg, rfl⟩ := hc
  obtain ⟨Q, hQdeg, rfl⟩ := hc'
  have hinj : Set.InjOn (⇑dom) T := fun a _ b _ h => dom.injective h
  -- P and Q agree on the ≥k nodes dom''T, both degree <k ⟹ equal
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hT
  have hPQ : P - Q = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (s := S.image (fun i => dom i)) ?_ ?_
    · have hcard2 : (S.image (fun i => dom i)).card = k := by
        rw [Finset.card_image_of_injective _ dom.injective, hScard]
      rw [hcard2]
      exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hPdeg hQdeg)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hiT : i ∈ T := hSsub hi
      have h1 : P.eval (dom i) = w i := hcag i hiT
      have h2 : Q.eval (dom i) = w i := hc'ag i hiT
      rw [eval_sub, h1, h2, sub_self]
  have : P = Q := sub_eq_zero.mp hPQ
  rw [this]

open Classical in
/-- A sub-Johnson list bound gives `ExplainableCoreSupply` with budget
`L · C(A, k+m+1)`. -/
theorem explainableCoreSupply_of_listBound (dom : Fin n ↪ F) {k m L A : ℕ}
    (hLB : SubJohnsonListBound dom k m L A) :
    ExplainableCoreSupply dom k m (L * (A.choose (k + m + 1))) := by
  intro w
  obtain ⟨hLcard, hAcap⟩ := hLB w
  classical
  set expl := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
    (fun T => ExplainableOn dom k w T) with hexpl
  -- a total explainer function (junk outside `expl`)
  set f : Finset (Fin n) → (Fin n → F) := fun T =>
    if h : ExplainableOn dom k w T then h.choose else 0 with hf
  have hf_mem : ∀ T ∈ expl, f T ∈ bigAgreeCodewords dom k m w := by
    intro T hT
    rw [hexpl, Finset.mem_filter] at hT
    obtain ⟨hTmem, hex⟩ := hT
    have hTcard : T.card = k + m + 1 := (Finset.mem_powersetCard.mp hTmem).2
    have hfc := hex.choose_spec
    simp only [hf, dif_pos hex]
    rw [bigAgreeCodewords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hfc.1, ?_⟩
    refine le_trans (le_of_eq hTcard.symm) (Finset.card_le_card ?_)
    intro i hi; rw [listAgreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hfc.2 i hi⟩
  have hf_sub : ∀ T ∈ expl, T ⊆ listAgreeSet (f T) w := by
    intro T hT
    rw [hexpl, Finset.mem_filter] at hT
    obtain ⟨-, hex⟩ := hT
    have hfc := hex.choose_spec
    simp only [hf, dif_pos hex]
    intro i hi; rw [listAgreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hfc.2 i hi⟩
  -- fibrewise over the explaining codeword
  rw [Finset.card_eq_sum_card_fiberwise hf_mem]
  calc ∑ c ∈ bigAgreeCodewords dom k m w, (expl.filter (fun T => f T = c)).card
      ≤ ∑ _c ∈ bigAgreeCodewords dom k m w, A.choose (k + m + 1) := by
        refine Finset.sum_le_sum (fun c hc => ?_)
        have hsub : expl.filter (fun T => f T = c)
            ⊆ (listAgreeSet c w).powersetCard (k + m + 1) := by
          intro T hT
          rw [Finset.mem_filter] at hT
          obtain ⟨hTexpl, hfc⟩ := hT
          have hTcard : T.card = k + m + 1 := by
            rw [hexpl, Finset.mem_filter] at hTexpl
            exact (Finset.mem_powersetCard.mp hTexpl.1).2
          rw [Finset.mem_powersetCard]
          exact ⟨hfc ▸ hf_sub T hTexpl, hTcard⟩
        calc (expl.filter (fun T => f T = c)).card
            ≤ ((listAgreeSet c w).powersetCard (k + m + 1)).card :=
              Finset.card_le_card hsub
          _ = (listAgreeSet c w).card.choose (k + m + 1) :=
              Finset.card_powersetCard _ _
          _ ≤ A.choose (k + m + 1) := Nat.choose_le_choose _ (hAcap c hc)
    _ = (bigAgreeCodewords dom k m w).card * A.choose (k + m + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ L * A.choose (k + m + 1) := Nat.mul_le_mul_right _ hLcard

/-- The budget supplied by the all-word list hypothesis is at least the total
number of cores of the given size. -/
theorem subJohnsonListBound_supply_budget (dom : Fin n ↪ F) {k m L A : ℕ}
    (h : SubJohnsonListBound dom k m L A) :
    n.choose (k + m + 1) ≤ L * A.choose (k + m + 1) :=
  (explainableCoreSupply_iff dom k m _).mp (explainableCoreSupply_of_listBound dom h)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.subJohnsonListBound_agreement_cap
#print axioms ProximityGap.Ownership.subJohnsonListBound_supply_budget
#print axioms ProximityGap.Ownership.explainer_unique
#print axioms ProximityGap.Ownership.explainableCoreSupply_of_listBound
