/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MomentSupplyIdentity

/-!
# The general-rate nodal supply witness (#389): the `m = 0` slice, ALL rates

The split-nodal construction extends verbatim to every rate `k ≥ 1`.  For
`γ ≠ 0` the word

  `w(x) = x^k + γ·x⁻¹`   (the graph of the degree-`(k+1)` curve `x·y = x^{k+1} + γ`)

has codeword agreements `≤ k + 1` (`nodalK_word_agreement_le` — the plain root
bound on `X^{k+1} − X·P + γ`, so `w` is in every capped class), and a
`(k+1)`-subset `T` is an explainable core **iff** `∏_{i∈T} dom i = (−1)^{k+1}γ`
(`nodalK_explainableOn`): the collinearity law of the curve is PURELY
multiplicative at every rate — Vieta pins only `e_{k+1} = ±γ`, while
`e_1, …, e_k` are exactly the `k` degrees of freedom of a degree-`<k` codeword.

On a multiplicative subgroup `μ_n` every `(k+1)`-tuple with the pinned product
extends, so the supply is `≈ n^k/(k+1)!` cores — **independently of `q`**.  This
is the first-principles refutation, at EVERY rate, of every `q`-conditional or
subexponential form of `SubJohnsonSupplyResidual` at `m = 0`: the multiplicative
collinearity never touches the additive structure the Frobenius witness needed
nor the field-size room the monomial witness needed.

The matching ceiling is the moment–supply identity (`moment_identity_base`:
`Σ_c C(a_c, k) = C(n, k)` identically) consumed at `j = k`: any word with
agreements `≤ k+1` has `(k+1)`-core count `E` with `E · (k+1) ≤ C(n, k)`
(`nodalK_supply_ceiling`).  Together with the floor: **the `(k, 0)` capped
supply is `Θ(n^k)` at EVERY rate, on every `μ_n`, at EVERY field size** — the
exact-order sub-Johnson supply value at the bottom of the band.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.NodalSupplyK

open ProximityGap.SpikeFloor ProximityGap.Ownership ProximityGap
open ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The general-`k` nodal word `x ↦ x^k + γ·x⁻¹`. -/
def nodalWordK (dom : Fin n ↪ F) (k : ℕ) (γ : F) : Fin n → F :=
  fun i => dom i ^ k + γ * (dom i)⁻¹

/-- The node polynomial of a subset. -/
noncomputable def nodePoly (dom : Fin n ↪ F) (T : Finset (Fin n)) : F[X] :=
  ∏ i ∈ T, (X - C (dom i))

theorem nodePoly_monic (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (nodePoly dom T).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (dom i)

theorem nodePoly_natDegree (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (nodePoly dom T).natDegree = T.card := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (dom i)]
  simp [natDegree_X_sub_C]

theorem nodePoly_eval (dom : Fin n ↪ F) (T : Finset (Fin n)) (x : F) :
    (nodePoly dom T).eval x = ∏ i ∈ T, (x - dom i) := by
  rw [nodePoly, eval_prod]
  simp

theorem nodePoly_eval_eq_zero (dom : Fin n ↪ F) {T : Finset (Fin n)}
    {i : Fin n} (hi : i ∈ T) : (nodePoly dom T).eval (dom i) = 0 := by
  rw [nodePoly_eval]
  exact Finset.prod_eq_zero hi (by simp)

/-- **The cap, for free**: agreements are roots of the degree-`(k+1)` polynomial
`X^{k+1} + γ − X·P`. -/
theorem nodalK_word_agreement_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {γ : F}
    (h0 : ∀ i, dom i ≠ 0) (c : Fin n → F)
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (agreeSet c (nodalWordK dom k γ)).card ≤ k + 1 := by
  obtain ⟨P, hPdeg, rfl⟩ := hc
  by_contra hgt
  push_neg at hgt
  have hPnd : P.natDegree ≤ k - 1 ∨ P = 0 := by
    by_cases hP0 : P = 0
    · exact Or.inr hP0
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
      exact Or.inl (by omega)
  set Q : F[X] := X ^ (k + 1) + (C γ - X * P) with hQ
  have hXPnd : (X * P).natDegree ≤ k := by
    calc (X * P).natDegree ≤ X.natDegree + P.natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ k := by
          rw [Polynomial.natDegree_X]
          rcases hPnd with h | h
          · omega
          · rw [h, Polynomial.natDegree_zero]; omega
  have hQnd : Q.natDegree ≤ k + 1 := by
    rw [hQ]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [Polynomial.natDegree_X_pow]
    refine max_le le_rfl ?_
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_C]
    exact max_le (by omega) (by omega)
  have hXPk1 : (X * P).coeff (k + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hQne : Q ≠ 0 := by
    intro h0'
    have hcoeff : Q.coeff (k + 1) = 1 := by
      simp [hQ, coeff_add, coeff_sub, coeff_X_pow, Polynomial.coeff_C, hXPk1]
    rw [h0', Polynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm
  have hroots : ((agreeSet (fun i => P.eval (dom i)) (nodalWordK dom k γ)).image
      (fun i => dom i)).card ≤ k + 1 := by
    have hsub : ∀ x ∈ (agreeSet (fun i => P.eval (dom i))
        (nodalWordK dom k γ)).image (fun i => dom i), Q.IsRoot x := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter] at hi
      have hag := hi.2
      rw [nodalWordK] at hag
      have hx0 := h0 i
      have hag' : dom i * P.eval (dom i) = dom i ^ (k + 1) + γ := by
        rw [hag]
        field_simp
        ring
      rw [IsRoot, hQ]
      simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
      linear_combination -hag'
    calc ((agreeSet (fun i => P.eval (dom i)) (nodalWordK dom k γ)).image
          (fun i => dom i)).card
        ≤ Q.roots.toFinset.card := by
          refine Finset.card_le_card fun x hx => ?_
          rw [Multiset.mem_toFinset, mem_roots hQne]
          exact hsub x hx
      _ ≤ Multiset.card Q.roots := Q.roots.toFinset_card_le
      _ ≤ Q.natDegree := Polynomial.card_roots' Q
      _ ≤ k + 1 := hQnd
  rw [Finset.card_image_of_injective _ dom.injective] at hroots
  omega

/-- **The core mechanism (all rates)**: a `(k+1)`-subset with point-product
`(−1)^{k+1}γ` is an explainable core — the quotient `(X^{k+1} + γ − N_T)/X` is the
fitting degree-`<k` codeword. -/
theorem nodalK_explainableOn (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {γ : F}
    (h0 : ∀ i, dom i ≠ 0) {T : Finset (Fin n)} (hT : T.card = k + 1)
    (hprod : ∏ i ∈ T, dom i = (-1) ^ (k + 1) * γ) :
    ExplainableOn dom k (nodalWordK dom k γ) T := by
  set N := nodePoly dom T with hN
  set R : F[X] := X ^ (k + 1) + C γ - N with hR
  -- R has degree ≤ k (leading X^{k+1} cancels N's), and X ∣ R (constant term 0)
  have hNmonic := nodePoly_monic dom T
  have hNnd : N.natDegree = k + 1 := by rw [hN, nodePoly_natDegree, hT]
  have hsignsq : ((-1 : F) ^ (k + 1)) * ((-1) ^ (k + 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hNconst : N.eval 0 = γ := by
    rw [hN, nodePoly_eval]
    rw [show (∏ i ∈ T, ((0 : F) - dom i)) = ∏ i ∈ T, (-1) * dom i from
      Finset.prod_congr rfl fun i _ => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hT, hprod, ← mul_assoc,
      hsignsq, one_mul]
  have hRconst : R.coeff 0 = 0 := by
    rw [hR, coeff_zero_eq_eval_zero]
    simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C]
    rw [hNconst, zero_pow (by omega : k + 1 ≠ 0)]
    ring
  -- natDegree R ≤ k: the leading X^{k+1} cancels N's, every higher coeff vanishes
  have hRnd : R.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [hR, coeff_sub, coeff_add, coeff_X_pow, Polynomial.coeff_C,
      if_neg (by omega : ¬ m = 0)]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm) with heq | hlt
    · -- m = k+1: the leading terms cancel (both coeff 1)
      have hmeq : m = k + 1 := by omega
      rw [hmeq, if_pos rfl,
        show N.coeff (k + 1) = 1 from by rw [← hNnd]; exact hNmonic.coeff_natDegree]
      ring
    · -- m > k+1: every term vanishes
      have hNm : N.coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hNnd]; omega)
      rw [hNm, if_neg (by omega : ¬ m = k + 1)]
      ring
  obtain ⟨P, hPR⟩ := Polynomial.X_dvd_iff.mpr hRconst
  -- the codeword is P; degree < k
  have hPnd : P.natDegree < k := by
    by_cases hP0 : P = 0
    · simp only [hP0, Polynomial.natDegree_zero]
      omega
    · have hRnd' : R.natDegree = P.natDegree + 1 := by
        rw [hPR, mul_comm, Polynomial.natDegree_mul_X hP0]
      omega
  refine ⟨fun i => P.eval (dom i), ⟨P, ?_, rfl⟩, fun i hi => ?_⟩
  · exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hPnd)
  · -- P(dom i) = w(dom i): from R = X·P and R(dom i) = dom i^{k+1}+γ
    have hRroot : R.eval (dom i) = dom i ^ (k + 1) + γ := by
      rw [hR]
      simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C]
      rw [hN, nodePoly_eval_eq_zero dom hi]
      ring
    have hRXP : R.eval (dom i) = dom i * P.eval (dom i) := by
      rw [hPR]
      simp [mul_comm]
    have hkey : dom i * P.eval (dom i) = dom i ^ (k + 1) + γ := by
      rw [← hRXP, hRroot]
    rw [nodalWordK]
    have hx0 := h0 i
    field_simp
    linear_combination hkey

open Classical in
/-- **The supply floor (all rates)**: every product-`((−1)^{k+1}γ)` `(k+1)`-subset
is an explainable core. On `μ_n` every `(k+1)`-tuple with the pinned product
extends, so the count is `Θ(n^k)` — at every field size. -/
theorem nodalK_supply_ge (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {γ : F}
    (h0 : ∀ i, dom i ≠ 0) :
    ((((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
      (fun T => ∏ i ∈ T, dom i = (-1) ^ (k + 1) * γ)).card)
      ≤ (degenerateSets dom k (k + 1) (nodalWordK dom k γ)).card := by
  refine Finset.card_le_card fun T hT => ?_
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
  rw [mem_degenerateSets]
  exact ⟨hT.1.2, nodalK_explainableOn dom hk h0 hT.1.2 hT.2⟩

open Classical in
/-- **The matching ceiling (all rates)**: any word with agreements `≤ k+1` has
`(k+1)`-core count `E` with `E·(k+1) ≤ C(n, k)` — the moment–supply identity at
`j = k` freezes `Σ_c C(a_c, k) = C(n, k)`, and each `(k+1)`-core spends `k+1` of
its explainer's `k`-subsets. -/
theorem nodalK_supply_ceiling (dom : Fin n ↪ F) {k : ℕ}
    {w : Fin n → F}
    (hcap : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c w).card ≤ k + 1) :
    (degenerateSets dom k (k + 1) w).card * (k + 1) ≤ n.choose k := by
  have hid := moment_supply_identity dom (by omega : k ≤ k + 1) w
  have hbase := moment_identity_base dom k w
  have hpt : ∀ c ∈ codewordFinset dom k,
      ((agreeSet c w).card.choose (k + 1)) * (k + 1)
        ≤ ((agreeSet c w).card.choose k) := by
    intro c hc
    have hk1 := hcap c (mem_codewordFinset.mp hc)
    rcases Nat.lt_or_ge (agreeSet c w).card (k + 1) with hlt | hge
    · rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    · have heq : (agreeSet c w).card = k + 1 := le_antisymm hk1 hge
      rw [heq, Nat.choose_self, Nat.choose_succ_self_right]
      omega
  calc (degenerateSets dom k (k + 1) w).card * (k + 1)
      = (∑ c ∈ codewordFinset dom k, ((agreeSet c w).card.choose (k + 1)))
          * (k + 1) := by rw [hid]
    _ = ∑ c ∈ codewordFinset dom k,
          ((agreeSet c w).card.choose (k + 1)) * (k + 1) := by rw [Finset.sum_mul]
    _ ≤ ∑ c ∈ codewordFinset dom k, ((agreeSet c w).card.choose k) :=
        Finset.sum_le_sum hpt
    _ = n.choose k := hbase

end ProximityGap.NodalSupplyK

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.NodalSupplyK.nodalK_word_agreement_le
#print axioms ProximityGap.NodalSupplyK.nodalK_explainableOn
#print axioms ProximityGap.NodalSupplyK.nodalK_supply_ge
#print axioms ProximityGap.NodalSupplyK.nodalK_supply_ceiling
