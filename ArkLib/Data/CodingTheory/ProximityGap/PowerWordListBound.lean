/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CorePartitionLemma
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# The power-word countermodel for every rate (#389, general `k`)

`CubicSupplyCountermodel` (`k = 2`) generalizes to every degree.  The right
"curve word" for `rsCode dom k` is `w(x) = x^{k+1}`: a `(k+1)`-subset `T` of the
domain is explainable by a degree-`<k` codeword **iff the values sum to zero**.

> **`powerWord_explainable`** — `T.card = k+1` and `∑_{i∈T} dom i = 0` ⟹
> `ExplainableOn dom k (powerWord dom k) T`.

Construction: `R := X^{k+1} − ∏_{i∈T}(X − xᵢ)` vanishes nowhere new (`R(xⱼ)=xⱼ^{k+1}`)
and has degree `≤ k−1` exactly when the `X^k`-coefficient `= ∑ xᵢ` vanishes
(`prod_X_sub_C_coeff_card_pred`: the next-to-leading coefficient of `∏(X−xᵢ)` is
`−∑ xᵢ`).  This is the `k=2` Sylvester sum `a+b+c=0` lifted to every `k`.

Exact list identity (`powerWord_list_eq_sumZero`): a root-count cap
(`powerWord_agreeSet_card_le`) says no degree-`<k` codeword can agree with `x^(k+1)`
on more than `k+1` points, so the sub-Johnson list at agreement `k+1` is exactly the
zero-sum `(k+1)`-subset fiber, with no overcount.

Consequence (`powerWord_supply_ge_sumZero`): for every `k`, the per-word supply of
`x^{k+1}` is `≥ #{(k+1)-subsets summing to 0}` — the domain's `(k+1)`-fold additive
energy.  On the full field this is `Θ(n^k) = Θ(C(n,k)/C(k+1,k))`, matching the
sub-Johnson list ceiling `rsCode_subJohnson_list_card_le` exactly: the ceiling is
**tight for every rate**.  On a multiplicative (smooth) subgroup it collapses to
the subgroup's additive-energy scale — the smooth suppression, for every `k`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PowerWord

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The power word `w(x) = (dom x)^{k+1}`. -/
def powerWord (dom : Fin n ↪ F) (k : ℕ) : Fin n → F := fun x => (dom x) ^ (k + 1)

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- **The general-`k` Sylvester mechanism**: a `(k+1)`-subset whose domain values
sum to zero is explainable by one degree-`<k` codeword. -/
theorem powerWord_explainable (dom : Fin n ↪ F) {k : ℕ} {T : Finset (Fin n)}
    (hT : T.card = k + 1) (hsum : ∑ i ∈ T, dom i = 0) :
    ExplainableOn dom k (powerWord dom k) T := by
  classical
  set Q : F[X] := ∏ i ∈ T, (X - C (dom i)) with hQ
  have hQmonic : Q.Monic := monic_prod_X_sub_C _ _
  have hQnd : Q.natDegree = k + 1 := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom i))]
    simp only [Polynomial.natDegree_X_sub_C]
    rw [Finset.sum_const, hT, smul_eq_mul, mul_one]
  set R : F[X] := X ^ (k + 1) - Q with hR
  refine ⟨fun x => R.eval (dom x), ⟨R, ?_, rfl⟩, ?_⟩
  · -- R.degree < k
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [hR, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases Nat.lt_or_ge m (k + 1) with hmlt | hmge
    · -- k ≤ m < k+1 ⟹ m = k: the X^k coefficient is ∑ xᵢ = 0
      have hmk : m = k := by omega
      subst hmk
      rw [if_neg (by omega)]
      have hvieta := Polynomial.prod_X_sub_C_coeff_card_pred T (fun i => dom i)
        (by rw [hT]; omega)
      rw [hT] at hvieta
      simp only [Nat.add_sub_cancel] at hvieta
      rw [← hQ] at hvieta
      rw [hvieta]
      simp only [hsum, neg_zero, sub_zero]
    · -- m ≥ k+1: the leading terms cancel / vanish
      rcases Nat.lt_or_ge (k + 1) m with hgt | hle
      · -- m > k+1
        rw [if_neg (by omega),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m)]
        ring
      · -- m = k+1
        have hmk1 : m = k + 1 := by omega
        subst hmk1
        rw [if_pos rfl]
        have hlead : Q.coeff (k + 1) = 1 := by rw [← hQnd]; exact hQmonic
        rw [hlead]; ring
  · -- agreement on T
    intro x hx
    change R.eval (dom x) = powerWord dom k x
    rw [hR, powerWord]
    have hprod0 : Q.eval (dom x) = 0 := by
      rw [hQ, Polynomial.eval_prod]
      refine Finset.prod_eq_zero hx ?_
      simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hprod0, sub_zero]

omit [Fintype F] [DecidableEq F] [NeZero n] in
/-- **The converse power-word mechanism**: any degree-`<k` explainer for
`w(x)=x^(k+1)` on a `(k+1)`-core forces that core's domain values to sum to zero.

This is the general-`k` version of the cubic collinearity identity's forward
direction.  The proof is quotient-rigidity: `X^(k+1) - P` and
`∏_{i∈T}(X-dom i)` are monic degree-`k+1` polynomials with the same `k+1`
distinct roots, so they are equal; comparing the `X^k` coefficient gives the
zero-sum condition. -/
theorem powerWord_explainable_imp_sumZero (dom : Fin n ↪ F) {k : ℕ}
    {T : Finset (Fin n)} (hT : T.card = k + 1)
    (h : ExplainableOn dom k (powerWord dom k) T) :
    ∑ i ∈ T, dom i = 0 := by
  classical
  obtain ⟨cw, ⟨P, hPdeg, rfl⟩, hagree⟩ := h
  set Q : F[X] := ∏ i ∈ T, (X - C (dom i)) with hQ
  have hQmonic : Q.Monic := monic_prod_X_sub_C _ _
  have hQnd : Q.natDegree = k + 1 := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom i))]
    simp only [Polynomial.natDegree_X_sub_C]
    rw [Finset.sum_const, hT, smul_eq_mul, mul_one]
  have hQdeg : Q.degree = ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hQmonic.ne_zero, hQnd]
  set D : F[X] := X ^ (k + 1) - P with hD
  have hXQlt : ((X : F[X]) ^ (k + 1) - Q).degree
      < ((k + 1 : ℕ) : WithBot ℕ) := by
    have hlt := Polynomial.degree_sub_lt (p := (X : F[X]) ^ (k + 1)) (q := Q)
      (by rw [degree_X_pow, hQdeg]) (pow_ne_zero (k + 1) X_ne_zero)
      (by rw [(monic_X_pow (k + 1)).leadingCoeff, hQmonic.leadingCoeff])
    simpa [degree_X_pow] using hlt
  have hPdeg' : P.degree < ((k + 1 : ℕ) : WithBot ℕ) :=
    lt_of_lt_of_le hPdeg (by exact_mod_cast (show k ≤ k + 1 by omega))
  have hDsubQdeg : (D - Q).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
    have hrewrite : D - Q = ((X : F[X]) ^ (k + 1) - Q) - P := by
      rw [hD]; ring
    rw [hrewrite]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hXQlt hPdeg')
  have hvan : ∀ x ∈ T.image dom, (D - Q).eval x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hDzero : D.eval (dom i) = 0 := by
      have ha : P.eval (dom i) = powerWord dom k i := hagree i hi
      rw [hD, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ha,
        powerWord, sub_self]
    have hQzero : Q.eval (dom i) = 0 := by
      rw [hQ, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hi (by simp [Polynomial.eval_sub, Polynomial.eval_X])
    rw [Polynomial.eval_sub, hDzero, hQzero, sub_self]
  have hzero : D - Q = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := T.image dom)
      (by rw [Finset.card_image_of_injective _ dom.injective, hT]; exact hDsubQdeg) hvan
  have hDQ : D = Q := sub_eq_zero.mp hzero
  have hQcoeff : Q.coeff k = 0 := by
    rw [← hDQ, hD, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    have hneq : ¬ k = k + 1 := by omega
    have hPcoeff : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_degree_lt hPdeg
    rw [if_neg hneq, hPcoeff]
    ring
  have hvieta := Polynomial.prod_X_sub_C_coeff_card_pred T (fun i => dom i)
    (by rw [hT]; omega)
  rw [hT] at hvieta
  simp only [Nat.add_sub_cancel] at hvieta
  rw [← hQ] at hvieta
  rw [hvieta] at hQcoeff
  exact neg_eq_zero.mp hQcoeff

omit [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- **Exact core characterization for the power word.**  On `(k+1)`-cores,
`x^(k+1)` is explainable by `rsCode dom k` exactly when the core has zero sum. -/
theorem powerWord_explainable_iff_sumZero (dom : Fin n ↪ F) {k : ℕ}
    {T : Finset (Fin n)} (hT : T.card = k + 1) :
    ExplainableOn dom k (powerWord dom k) T ↔ ∑ i ∈ T, dom i = 0 :=
  ⟨powerWord_explainable_imp_sumZero dom hT, powerWord_explainable dom hT⟩

omit [Fintype F] [NeZero n] in
open Classical in
/-- **Root-count cap for the power word.**  A degree-`< k` codeword cannot agree
with `x^(k+1)` on more than `k+1` domain points. -/
theorem powerWord_agreeSet_card_le (dom : Fin n ↪ F) {k : ℕ} {P : F[X]}
    (hPdeg : P.degree < (k : WithBot ℕ)) :
    (agreeSet (fun i => P.eval (dom i)) (powerWord dom k)).card ≤ k + 1 := by
  classical
  set A := agreeSet (fun i => P.eval (dom i)) (powerWord dom k) with hA
  set Q : F[X] := X ^ (k + 1) - P with hQ
  have hPdeg' : P.degree < ((k + 1 : ℕ) : WithBot ℕ) :=
    lt_of_lt_of_le hPdeg (by exact_mod_cast (show k ≤ k + 1 by omega))
  have hQne : Q ≠ 0 := by
    intro hzero
    have hXP : (X ^ (k + 1) : F[X]) = P := by
      rw [hQ] at hzero
      exact sub_eq_zero.mp hzero
    have hlt : (X ^ (k + 1) : F[X]).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
      rw [hXP]
      exact hPdeg'
    rw [degree_X_pow] at hlt
    exact (lt_irrefl _ hlt)
  have hQdeg : Q.degree ≤ ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [hQ]
    refine le_trans (degree_sub_le _ _) (max_le ?_ ?_)
    · exact le_of_eq (degree_X_pow (k + 1))
    · exact le_of_lt hPdeg'
  have hQnat : Q.natDegree ≤ k + 1 := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact hQdeg
  have hroots : (A.image dom).card ≤ Q.roots.toFinset.card := by
    refine Finset.card_le_card ?_
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQne]
    have hiagree : P.eval (dom i) = powerWord dom k i := by
      rw [hA] at hi
      exact (Finset.mem_filter.mp hi).2
    rw [hQ, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      hiagree, powerWord, sub_self]
  calc A.card
      = (A.image dom).card := (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ Q.roots.toFinset.card := hroots
    _ ≤ Q.roots.card := Q.roots.toFinset_card_le
    _ ≤ Q.natDegree := Q.card_roots'
    _ ≤ k + 1 := hQnat

open Classical in
/-- **Exact list identity for the power word.**  The list at agreement `k+1`
for `w(x)=x^(k+1)` is exactly the zero-sum `(k+1)`-subset fibre of the domain. -/
theorem powerWord_list_eq_sumZero (dom : Fin n ↪ F) (k : ℕ) :
    ((Finset.univ : Finset (Fin n → F)).filter (fun c =>
        c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ k + 1 ≤ (agreeSet c (powerWord dom k)).card)).card
      = (((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
          (fun T => ∑ i ∈ T, dom i = 0)).card := by
  classical
  set w := powerWord dom k with hw
  refine Finset.card_bij (fun c _ => agreeSet c w) ?_ ?_ ?_
  · intro c hc
    obtain ⟨-, hcmem, hge⟩ := Finset.mem_filter.mp hc
    obtain ⟨P, hPdeg, rfl⟩ := hcmem
    have hle : (agreeSet (fun i => P.eval (dom i)) w).card ≤ k + 1 := by
      simpa [w, hw] using powerWord_agreeSet_card_le dom (k := k) (P := P) hPdeg
    have hcard : (agreeSet (fun i => P.eval (dom i)) w).card = k + 1 :=
      le_antisymm hle hge
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    exact (powerWord_explainable_iff_sumZero dom hcard).mp
      ⟨fun i => P.eval (dom i), ⟨P, hPdeg, rfl⟩,
        fun i hi => (Finset.mem_filter.mp hi).2⟩
  · intro c hc c' hc' heq
    obtain ⟨-, hcmem, hge⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hc'mem, -⟩ := Finset.mem_filter.mp hc'
    have heqA : agreeSet c w = agreeSet c' w := heq
    refine ProximityGap.PairRank.explainable_core_explainer_unique (k := k) dom
      (le_trans (Nat.le_succ k) hge) hcmem hc'mem
      (fun i hi => (Finset.mem_filter.mp hi).2) ?_
    intro i hi
    have hi' : i ∈ agreeSet c' w := by
      rw [← heqA]
      exact hi
    exact (Finset.mem_filter.mp hi').2
  · intro T hT
    obtain ⟨hTp, hsum⟩ := Finset.mem_filter.mp hT
    obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTp
    obtain ⟨c, hcmem, hagree⟩ := (powerWord_explainable_iff_sumZero dom hTcard).mpr hsum
    obtain ⟨P, hPdeg, rfl⟩ := hcmem
    have hTsub : T ⊆ agreeSet (fun i => P.eval (dom i)) w := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree i hi⟩
    have hge : k + 1 ≤ (agreeSet (fun i => P.eval (dom i)) w).card := by
      calc k + 1 = T.card := hTcard.symm
        _ ≤ (agreeSet (fun i => P.eval (dom i)) w).card := Finset.card_le_card hTsub
    refine ⟨fun i => P.eval (dom i), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨P, hPdeg, rfl⟩, hge⟩, ?_⟩
    have hle : (agreeSet (fun i => P.eval (dom i)) w).card ≤ k + 1 := by
      simpa [w, hw] using powerWord_agreeSet_card_le dom (k := k) (P := P) hPdeg
    have heq : T = agreeSet (fun i => P.eval (dom i)) w :=
      Finset.eq_of_subset_of_card_le hTsub (by
        rw [hTcard]
        exact hle)
    exact heq.symm

omit [Fintype F] [NeZero n] in
open Classical in
/-- **The general-`k` supply lower bound**: the power word's explainable
`(k+1)`-cores include every `(k+1)`-subset summing to zero — the domain's
`(k+1)`-fold additive energy. -/
theorem powerWord_supply_ge_sumZero (dom : Fin n ↪ F) {k B : ℕ}
    (hB : ExplainableCoreSupply dom k 0 B) :
    ((Finset.univ.powersetCard (k + 1)).filter
        (fun T => ∑ i ∈ T, dom i = 0)).card ≤ B := by
  classical
  refine le_trans (Finset.card_le_card ?_) (hB (powerWord dom k))
  intro T hT
  obtain ⟨hTmem, hsum⟩ := Finset.mem_filter.mp hT
  obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
  exact Finset.mem_filter.mpr ⟨hTmem, powerWord_explainable dom hTcard hsum⟩

end ProximityGap.PowerWord

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PowerWord.powerWord_explainable
#print axioms ProximityGap.PowerWord.powerWord_explainable_imp_sumZero
#print axioms ProximityGap.PowerWord.powerWord_explainable_iff_sumZero
#print axioms ProximityGap.PowerWord.powerWord_agreeSet_card_le
#print axioms ProximityGap.PowerWord.powerWord_list_eq_sumZero
#print axioms ProximityGap.PowerWord.powerWord_supply_ge_sumZero
