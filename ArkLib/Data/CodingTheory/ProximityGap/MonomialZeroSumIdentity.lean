/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CubicOrchardIdentity

/-!
# THE MONOMIAL ZERO-SUM LAW at every rate (#389)

The exact sub-Johnson list size of the monomial word `x^(k+1)` at dimension `k` and
matching agreement `k+1`, on EVERY domain — the general-rate law of which the cubic
orchard identity (`cubic_list_eq_zeroSum`, `k=2`) is the first case:

> **`monomial_list_eq_zeroSum`** — for `1 ≤ k`, the word `w = x^(k+1)`:
> `#{c ∈ rsCode(dom,k) : |agreeSet(c,w)| ≥ k+1} = #{T ⊆ dom : |T| = k+1, Σ T = 0}`.

Mechanism (Vieta): a degree-`<k` codeword `P` agrees with `x^(k+1)` exactly at the roots
of the monic degree-`(k+1)` polynomial `Q = X^(k+1) − P`.  Since `P` carries no `X^k` term,
`Q.nextCoeff = 0`; and for the `k+1` distinct agreement values, `Q = ∏(X − dom i)` whose
`nextCoeff` is `−Σ dom i` (`prod_X_sub_C_nextCoeff`).  Hence `Σ = 0`, and no codeword agrees
on `k+2` points (a degree-`(k+1)` polynomial has `≤ k+1` roots).  Conversely each zero-sum
`(k+1)`-subset `T` yields `P = X^(k+1) − ∏_{i∈T}(X − dom i)` of degree `≤ k−1` agreeing on `T`.

Probe `probe_monomial_zerosum_general.py`: verified at `k = 2,3,4` (lists `14,20,24 /
35,45,125 / 93,364`).  The `k=2` slice is the orchard problem; combined with the scaling
reduction (`ordered_zerosum_sum_eq`) this pins the exact smooth-domain list size of the
monomial word at every rate.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The monomial Vieta sum law**: if a degree-`<k` codeword agrees with `x^(k+1)` on a
`(k+1)`-set `S` of indices, then `Σ_{i∈S} dom i = 0`. -/
theorem monomial_agree_sum_zero (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {P : Polynomial F} (hPdeg : P.degree < (k : ℕ))
    {S : Finset (Fin n)} (hScard : S.card = k + 1)
    (hagree : ∀ i ∈ S, P.eval (dom i) = (dom i) ^ (k + 1)) :
    ∑ i ∈ S, dom i = 0 := by
  classical
  set Q : Polynomial F := X ^ (k + 1) - P with hQ
  have hPlt1 : P.degree < ((k + 1 : ℕ) : WithBot ℕ) :=
    lt_of_lt_of_le hPdeg (by exact_mod_cast Nat.le_succ k)
  have hQmonic : Q.Monic := monic_X_pow_sub hPlt1
  -- Q has degree k+1
  have hdegXpow : (X ^ (k + 1) : Polynomial F).degree = (k + 1 : ℕ) := by
    rw [Polynomial.degree_X_pow]
  have hPltX : P.degree < (X ^ (k + 1) : Polynomial F).degree := by
    rw [hdegXpow]
    exact lt_of_lt_of_le hPdeg (by exact_mod_cast Nat.le_succ k)
  have hQdeg : Q.degree = (k + 1 : ℕ) := by
    rw [hQ, Polynomial.degree_sub_eq_left_of_degree_lt hPltX, hdegXpow]
  have hQnatDeg : Q.natDegree = k + 1 := Polynomial.natDegree_eq_of_degree_eq_some hQdeg
  -- the dom-values on S are roots of Q
  have hroot : ∀ i ∈ S, (X - C (dom i)) ∣ Q := by
    intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, hQ]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hagree i hi]
    ring
  -- R = ∏ (X - dom i) over S
  set R : Polynomial F := ∏ i ∈ S, (X - C (dom i)) with hR
  have hRmonic : R.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have hRnatDeg : R.natDegree = k + 1 := by
    rw [hR, Polynomial.natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero _)]
    simp [hScard]
  -- R ∣ Q (distinct roots ⟹ coprime linear factors)
  have hcop : (↑S : Set (Fin n)).Pairwise
      (fun i j => IsCoprime (X - C (dom i)) (X - C (dom j))) := by
    intro i _ j _ hij
    exact (Polynomial.pairwise_coprime_X_sub_C dom.injective) hij
  have hRdvd : R ∣ Q := Finset.prod_dvd_of_coprime hcop hroot
  -- R = Q (both monic, R ∣ Q, equal natDegree)
  have hReqQ : R = Q := by
    obtain ⟨D, hD⟩ := hRdvd
    have hDmonic : D.Monic := by
      have := hQmonic
      rw [hD] at this
      exact (hRmonic.of_mul_monic_left this)
    have hDdeg : D.natDegree = 0 := by
      have hQnd : Q.natDegree = R.natDegree + D.natDegree := by
        rw [hD, Polynomial.natDegree_mul hRmonic.ne_zero hDmonic.ne_zero]
      omega
    have hD1 : D = 1 := hDmonic.natDegree_eq_zero.mp hDdeg
    rw [hD, hD1, mul_one]
  -- nextCoeff: Q.nextCoeff = 0 = R.nextCoeff = -Σ dom i
  have hQnext : Q.nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos (by omega : 0 < Q.natDegree), hQnatDeg, hQ]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    have : P.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hPdeg (le_refl _))
    simp [this]
  have hRnext : R.nextCoeff = -∑ i ∈ S, dom i := by
    rw [hR, Polynomial.prod_X_sub_C_nextCoeff]
  rw [hReqQ, hQnext] at hRnext
  linear_combination hRnext

open Classical in
/-- **THE MONOMIAL ZERO-SUM LAW**: the exact sub-Johnson list size of `x^(k+1)` at
dimension `k`, agreement `k+1`, equals the zero-sum `(k+1)`-subset count, on EVERY domain. -/
theorem monomial_list_eq_zeroSum (dom : Fin n ↪ F) (k : ℕ) (hk : 1 ≤ k) :
    ((Finset.univ : Finset (Fin n → F)).filter (fun c =>
        c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ (k + 1) ≤ (agreeSet c (fun i => (dom i) ^ (k + 1))).card)).card
      = (((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
          (fun T => ∑ i ∈ T, dom i = 0)).card := by
  classical
  set w : Fin n → F := fun i => (dom i) ^ (k + 1) with hw
  -- agreement of a listed codeword is EXACTLY k+1
  have hcard : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (k + 1) ≤ (agreeSet c w).card → (agreeSet c w).card = k + 1 := by
    intro c hmem hge
    obtain ⟨P, hPdeg, rfl⟩ := hmem
    refine le_antisymm ?_ hge
    -- agreement points inject (via dom) into the roots of Q = X^(k+1) - P
    set Q : Polynomial F := X ^ (k + 1) - P with hQ
    have hPlt1 : P.degree < ((k + 1 : ℕ) : WithBot ℕ) :=
      lt_of_lt_of_le hPdeg (by exact_mod_cast Nat.le_succ k)
    have hQmonic : Q.Monic := monic_X_pow_sub hPlt1
    have hdegXpow : (X ^ (k + 1) : Polynomial F).degree = (k + 1 : ℕ) :=
      Polynomial.degree_X_pow _
    have hPltX : P.degree < (X ^ (k + 1) : Polynomial F).degree := by
      rw [hdegXpow]; exact hPlt1
    have hQdeg : Q.natDegree = k + 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some
        (by rw [hQ, Polynomial.degree_sub_eq_left_of_degree_lt hPltX, hdegXpow])
    have himg : (agreeSet (fun i => P.eval (dom i)) w).image dom ⊆ Q.roots.toFinset := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have heval := (Finset.mem_filter.mp hi).2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hQmonic.ne_zero,
        Polynomial.IsRoot.def, hQ]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [show w i = (dom i) ^ (k + 1) from rfl] at heval
      rw [← heval]; ring
    calc (agreeSet (fun i => P.eval (dom i)) w).card
        = ((agreeSet (fun i => P.eval (dom i)) w).image dom).card :=
          (Finset.card_image_of_injective _ dom.injective).symm
      _ ≤ Q.roots.toFinset.card := Finset.card_le_card himg
      _ ≤ Q.roots.card := Multiset.toFinset_card_le _
      _ ≤ Q.natDegree := Polynomial.card_roots' _
      _ = k + 1 := hQdeg
  refine Finset.card_bij (fun c _ => agreeSet c w) ?_ ?_ ?_
  · -- maps into the zero-sum (k+1)-subsets
    intro c hc
    obtain ⟨-, hmem, hge⟩ := Finset.mem_filter.mp hc
    have hexact := hcard c hmem hge
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hexact⟩, ?_⟩
    obtain ⟨P, hPdeg, rfl⟩ := hmem
    exact monomial_agree_sum_zero dom hk hPdeg hexact
      (fun i hi => (Finset.mem_filter.mp hi).2)
  · -- injective: k agreement points determine the codeword
    intro c hc c' hc' heq
    obtain ⟨-, hmem, hge⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hmem', -⟩ := Finset.mem_filter.mp hc'
    have heq' : agreeSet c w = agreeSet c' w := heq
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
      (by omega : k ≤ (agreeSet c w).card)
    have hTsub' : T ⊆ agreeSet c' w := by rw [← heq']; exact hTsub
    refine explainable_core_explainer_unique (k := k) dom
      (le_of_eq hTcard.symm) hmem hmem'
      (fun i hi => (Finset.mem_filter.mp (hTsub hi)).2)
      (fun i hi => (Finset.mem_filter.mp (hTsub' hi)).2)
  · -- surjective: each zero-sum (k+1)-subset is realized by its interpolating word
    intro T hT
    obtain ⟨hTmem, hTsum⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
    set R : Polynomial F := ∏ i ∈ T, (X - C (dom i)) with hR
    have hRmonic : R.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
    have hRnatDeg : R.natDegree = k + 1 := by
      rw [hR, Polynomial.natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero _)]
      simp [hTcard]
    have hRnext : R.nextCoeff = 0 := by
      rw [hR, Polynomial.prod_X_sub_C_nextCoeff, hTsum, neg_zero]
    set P : Polynomial F := X ^ (k + 1) - R with hP
    -- deg P < k : the top two coefficients of X^(k+1) and R cancel
    have hRk : R.coeff k = 0 := by
      have h := hRnext
      rwa [Polynomial.nextCoeff_of_natDegree_pos (by omega : 0 < R.natDegree),
        hRnatDeg, Nat.add_sub_cancel] at h
    have hPcoeff : ∀ m : ℕ, k ≤ m → P.coeff m = 0 := by
      intro m hm
      rw [hP, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy m (k + 1) with hlt | heq | hgt
      · rw [if_neg (by omega : ¬ m = k + 1)]
        have hmk : m = k := by omega
        rw [hmk, hRk]; ring
      · subst heq
        rw [if_pos rfl, ← hRnatDeg, hRmonic.coeff_natDegree]; ring
      · rw [if_neg (by omega : ¬ m = k + 1),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < m)]
        ring
    have hPdeg : P.degree < (k : ℕ) := by
      have hle : P.degree ≤ ((k - 1 : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_le_iff_coeff_zero]
        intro m hm
        have hkm : k ≤ m := by
          have hlt : (k - 1 : ℕ) < m := by exact_mod_cast hm
          omega
        exact hPcoeff m hkm
      exact lt_of_le_of_lt hle (by exact_mod_cast (show k - 1 < k by omega))
    have hPmem : (fun i => P.eval (dom i)) ∈ (rsCode dom k : Submodule F (Fin n → F)) :=
      ⟨P, hPdeg, rfl⟩
    have hagr : ∀ i ∈ T, P.eval (dom i) = w i := by
      intro i hi
      have hRroot : R.eval (dom i) = 0 := by
        rw [hR, Polynomial.eval_prod]
        refine Finset.prod_eq_zero hi ?_
        simp
      rw [hP]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hRroot]
      simp [hw]
    have hTsubA : T ⊆ agreeSet (fun i => P.eval (dom i)) w := fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagr i hi⟩
    have hge : (k + 1) ≤ (agreeSet (fun i => P.eval (dom i)) w).card := by
      calc (k + 1) = T.card := hTcard.symm
      _ ≤ _ := Finset.card_le_card hTsubA
    refine ⟨fun i => P.eval (dom i),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPmem, hge⟩, ?_⟩
    have hexact := hcard _ hPmem hge
    exact (Finset.eq_of_subset_of_card_le hTsubA (by omega)).symm

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.monomial_agree_sum_zero
#print axioms ProximityGap.PairRank.monomial_list_eq_zeroSum
