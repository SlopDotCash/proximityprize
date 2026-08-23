/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CensusLaw

/-!
# The constrained census law: general code degree (the O138/O139 law)

`KKH26CensusLaw.lean` pins the bad scalars of the adjacent monomial pair `(X^a, X^{a−1})`
against codes of degree `≤ a − 2` (the `k = a − 1` case). This file proves the general-`k`
law discovered in DISPROOF_LOG O138 and measured inside the prize window in O139: against
polynomials of degree `< k` (any `1 ≤ k`, `k + 1 ≤ a`), a scalar `λ` is bad at agreement
threshold `a` over a finite evaluation set `H` **iff** there is an `a`-subset `T ⊆ H` whose
vanishing polynomial `∏_{x∈T}(X − x)` has zero coefficients in the constrained band
(degrees `a − j` for `2 ≤ j ≤ a − k`, equivalently `e₂(T) = … = e_{a−k}(T) = 0`) and
`λ = −∑ T`.

Probe ground truth (exact): the (12,6) flat numerator (12 at every p ∈ {13,37,61}) is this
census at `a = 9, k = 6`; the window-interior verdicts at (16,4) — field saturation at
`a = k+1`, field-dependence at one constraint, **emptiness** (family death) at two
constraints for `p ≥ 97` — are this census at `a ∈ {5,6,7}`
(`scripts/probes/probe_o138_flat_numerator_solved.py`,
`probe_o139_window_interior_census.py`).

Consequence: the entire contribution of the adjacent-pair family to the δ* upper bracket is
the solvability theory of the vanishing-power-sum system `e₂ = … = e_{a−k} = 0` over
`a`-subsets of a multiplicative subgroup — pure additive combinatorics/vanishing-sums
territory, with the proven `k = a − 1` law as the unconstrained base case.

## References
* Issue #357 (O138/O139); [KKH26] ePrint 2026/782 (the fiber construction this generalizes).
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The constrained band of the vanishing polynomial is zero: coefficients at degrees
`a − j` for `2 ≤ j ≤ a − k` (equivalently, the elementary symmetric functions
`e₂(T), …, e_{a−k}(T)` all vanish). -/
def ConstrainedBandZero (T : Finset F) (a k : ℕ) : Prop :=
  ∀ j, 2 ≤ j → j ≤ a - k → (∏ x ∈ T, (X - C x)).coeff (a - j) = 0

/-- **Forward half: a bad scalar yields a constrained `a`-subset.** Same monic-root-forcing
as `subsetSum_of_badScalar`, plus coefficient extraction across the constrained band. -/
theorem constrainedSubsetSum_of_badScalar {H : Finset F} {a k : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) {lam : F}
    {q : Polynomial F} (hq : q.natDegree ≤ k - 1)
    (hagree : a ≤ (lineAgreeSet H a lam q).card) :
    ∃ T ⊆ H, T.card = a ∧ ConstrainedBandZero T a k ∧ lam = -∑ x ∈ T, x := by
  classical
  have hr2 : 2 ≤ a := by omega
  have hq' : q.natDegree ≤ a - 2 := by omega
  obtain ⟨hmonic, hdeg⟩ := linePoly_monic hr2 lam hq'
  set T : Finset F := lineAgreeSet H a lam q with hT
  have hTH : T ⊆ H := Finset.filter_subset _ _
  have hTcard : T.card = a := le_antisymm (agreement_card_le hr2 lam hq') hagree
  -- `linePoly = ∏_{x∈T}(X − x)`, exactly as in the base law.
  set Q : Polynomial F := ∏ x ∈ T, (X - C x) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c
  have hQdeg : Q.natDegree = a := by
    rw [hQ, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hTcard]
  have hPQ : linePoly a lam q = Q := by
    by_contra hne
    have hsubne : linePoly a lam q - Q ≠ 0 := sub_ne_zero.mpr hne
    have hroots : ∀ x ∈ T, (linePoly a lam q - Q).IsRoot x := by
      intro x hx
      have h1 : (linePoly a lam q).IsRoot x := isRoot_linePoly_of_mem_agree hx
      have h2 : Q.IsRoot x := by
        rw [hQ]
        simp only [IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
        exact Finset.prod_eq_zero hx (by ring)
      simp only [IsRoot.def, eval_sub] at h1 h2 ⊢
      rw [h1, h2, sub_zero]
    have hdegsub : (linePoly a lam q - Q).natDegree < a := by
      have hcoeffr : (linePoly a lam q - Q).coeff a = 0 := by
        rw [coeff_sub]
        have h1 : (linePoly a lam q).coeff a = 1 := by
          have := hmonic.coeff_natDegree
          rwa [hdeg] at this
        have h2 : Q.coeff a = 1 := by
          have := hQmonic.coeff_natDegree
          rwa [hQdeg] at this
        rw [h1, h2, sub_self]
      have hdegle : (linePoly a lam q - Q).natDegree ≤ a := by
        refine le_trans (natDegree_sub_le _ _) ?_
        rw [hdeg, hQdeg]; simp
      rcases lt_or_eq_of_le hdegle with h | h
      · exact h
      · exfalso
        have hlc : (linePoly a lam q - Q).leadingCoeff = 0 := by
          rw [leadingCoeff, h, hcoeffr]
        exact hsubne (leadingCoeff_eq_zero.mp hlc)
    have hsubroots : T ⊆ (linePoly a lam q - Q).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hsubne]
      exact hroots x hx
    have : a ≤ (linePoly a lam q - Q).natDegree := by
      calc a = T.card := hTcard.symm
        _ ≤ (linePoly a lam q - Q).roots.toFinset.card := Finset.card_le_card hsubroots
        _ ≤ Multiset.card (linePoly a lam q - Q).roots := Multiset.toFinset_card_le _
        _ ≤ (linePoly a lam q - Q).natDegree := (linePoly a lam q - Q).card_roots'
    omega
  refine ⟨T, hTH, hTcard, ?_, ?_⟩
  · -- The constrained band: `Q.coeff (a − j) = linePoly.coeff (a − j) = −q.coeff (a − j) = 0`.
    intro j hj2 hjk
    rw [← hQ, ← hPQ]
    unfold linePoly
    have hxa : (X ^ a : Polynomial F).coeff (a - j) = 0 := by
      rw [coeff_X_pow]
      simp [show ¬ a = a - j by omega, show ¬ a - j = a by omega]
    have hxa1 : (X ^ (a - 1) : Polynomial F).coeff (a - j) = 0 := by
      rw [coeff_X_pow]
      simp [show ¬ a - 1 = a - j by omega, show ¬ a - j = a - 1 by omega]
    have hqc : q.coeff (a - j) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < a - j)
    rw [coeff_sub, coeff_add, coeff_C_mul, hxa, hxa1, hqc]
    ring
  · -- The `X^{a−1}` coefficient: Vieta.
    have hlhs : (linePoly a lam q).coeff (a - 1) = lam := by
      unfold linePoly
      have h2 : q.coeff (a - 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < a - 1)
      have hxr : (X ^ a : Polynomial F).coeff (a - 1) = 0 := by
        rw [coeff_X_pow]
        simp [show ¬ a = a - 1 by omega, show ¬ a - 1 = a by omega]
      have hxr1 : (X ^ (a - 1) : Polynomial F).coeff (a - 1) = 1 := by
        rw [coeff_X_pow]
        simp
      rw [coeff_sub, coeff_add, coeff_C_mul, hxr, hxr1, h2]
      ring
    have hrhs : Q.coeff (a - 1) = -∑ x ∈ T, x := by
      have h1 : Q.nextCoeff = -∑ x ∈ T, x := by
        rw [hQ]
        exact prod_X_sub_C_nextCoeff (fun x => x)
      have h2 : Q.nextCoeff = Q.coeff (Q.natDegree - 1) :=
        nextCoeff_of_natDegree_pos (by rw [hQdeg]; omega)
      rw [h2, hQdeg] at h1
      exact h1
    rw [hPQ, hrhs] at hlhs
    exact hlhs.symm

/-- **Backward half: every constrained `a`-subset realizes its sum as a bad scalar.** The
explaining polynomial is `q := X^a + λX^{a−1} − ∏_T(X − x)`; the constrained band makes its
degree drop below `k`. -/
theorem badScalar_of_constrainedSubsetSum {H : Finset F} {a k : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a)
    {T : Finset F} (hTH : T ⊆ H) (hTcard : T.card = a)
    (hband : ConstrainedBandZero T a k) :
    ∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧
      a ≤ (lineAgreeSet H a (-∑ x ∈ T, x) q).card := by
  classical
  set Q : Polynomial F := ∏ x ∈ T, (X - C x) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c
  have hQdeg : Q.natDegree = a := by
    rw [hQ, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hTcard]
  set lam : F := -∑ x ∈ T, x with hlam
  set q : Polynomial F := X ^ a + C lam * X ^ (a - 1) - Q with hq
  have hQa : Q.coeff a = 1 := by
    have := hQmonic.coeff_natDegree
    rwa [hQdeg] at this
  have hQa1 : Q.coeff (a - 1) = -∑ x ∈ T, x := by
    have h1 : Q.nextCoeff = -∑ x ∈ T, x := by
      rw [hQ]
      exact prod_X_sub_C_nextCoeff (fun x => x)
    have h2 : Q.nextCoeff = Q.coeff (Q.natDegree - 1) :=
      nextCoeff_of_natDegree_pos (by rw [hQdeg]; omega)
    rw [h2, hQdeg] at h1
    exact h1
  have hqdeg : q.natDegree ≤ k - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    -- `m > k − 1`, i.e. `m ≥ k`. Split: `m > a`, `m = a`, `m = a − 1`, or `m = a − j`
    -- for some `j ∈ [2, a − k]`.
    have hmk : k ≤ m := by omega
    rw [hq, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X_pow]
    rcases Nat.lt_or_ge a m with hcase | hcase
    · -- `m > a`: every term is zero.
      have hQm : Q.coeff m = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m)
      simp [show ¬ a = m by omega, show ¬ a - 1 = m by omega,
        show ¬ m = a by omega, show ¬ m = a - 1 by omega, hQm]
    · rcases Nat.eq_or_lt_of_le hcase with heq | hlt
      · -- `m = a`.
        rw [heq]
        simp [show ¬ a = a - 1 by omega, show ¬ a - 1 = a by omega, hQa]
      · rcases Nat.eq_or_lt_of_le (by omega : m ≤ a - 1) with heq1 | hlt1
        · -- `m = a − 1`.
          rw [heq1]
          simp [show ¬ a = a - 1 by omega, show ¬ a - 1 = a by omega, hQa1, hlam]
        · -- `m = a − j` for `j := a − m ∈ [2, a − k]`: the constrained band.
          have hband' : Q.coeff m = 0 := by
            have := hband (a - m) (by omega) (by omega)
            rwa [show a - (a - m) = m by omega] at this
          simp [show ¬ a = m by omega, show ¬ a - 1 = m by omega,
            show ¬ m = a by omega, show ¬ m = a - 1 by omega, hband']
  refine ⟨q, hqdeg, ?_⟩
  have hsub : T ⊆ lineAgreeSet H a lam q := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨hTH hx, ?_⟩
    have hQx : Q.eval x = 0 := by
      rw [hQ]
      simp only [eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero hx (by ring)
    rw [hq]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, hQx]
    ring
  calc a = T.card := hTcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **THE CONSTRAINED CENSUS LAW (general code degree).** Against polynomials of degree
`< k` over any finite evaluation set `H` in any field, the bad scalars of the adjacent
monomial pair `(X^a, X^{a−1})` at agreement threshold `a` are exactly the negated sums of
the `a`-subsets whose vanishing polynomial has zero constrained band
(`e₂ = … = e_{a−k} = 0`). The `k = a − 1` case (empty band) is `badScalar_iff_subsetSum`. -/
theorem badScalar_iff_constrainedSubsetSum (H : Finset F) {a k : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (lam : F) :
    (∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧ a ≤ (lineAgreeSet H a lam q).card) ↔
      (∃ T ⊆ H, T.card = a ∧ ConstrainedBandZero T a k ∧ lam = -∑ x ∈ T, x) := by
  constructor
  · rintro ⟨q, hq, hagree⟩
    exact constrainedSubsetSum_of_badScalar hk hka hq hagree
  · rintro ⟨T, hTH, hTcard, hband, rfl⟩
    exact badScalar_of_constrainedSubsetSum hk hka hTH hTcard hband

/-! ## Source audit -/

#print axioms constrainedSubsetSum_of_badScalar
#print axioms badScalar_of_constrainedSubsetSum
#print axioms badScalar_iff_constrainedSubsetSum

end ArkLib.ProximityGap.KKH26
