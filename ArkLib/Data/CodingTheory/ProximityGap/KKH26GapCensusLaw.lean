/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ConstrainedCensusLaw

/-!
# The gap census law: arbitrary two-monomial stacks (the masquerade hierarchy, O141/O142)

`KKH26CensusLaw.lean` (adjacent pair, full-degree code) and `KKH26ConstrainedCensusLaw.lean`
(adjacent pair, general code degree) are the gap-1 cases of the general **two-monomial law**
proved here: for the stack `(X^A, X^B)` (`k ≤ B < A`) against polynomials of degree `< k`,
a scalar `λ` is bad at agreement threshold `A` over a finite evaluation set `H` **iff** some
`A`-subset `T ⊆ H` satisfies

* the **outer band**: `coeff (A − j) (∏_{x∈T}(X − x)) = 0` for `1 ≤ j ≤ A − B − 1`
  (equivalently `e₁(T) = … = e_{A−B−1}(T) = 0`),
* the **pivot**: `λ = coeff B (∏_{x∈T}(X − x))` (i.e. `λ = (−1)^{A−B} e_{A−B}(T)`),
* the **inner band**: `coeff (A − j) (∏_{x∈T}(X − x)) = 0` for `A − B + 1 ≤ j ≤ A − k`.

In the fake-point/masquerade language of DISPROOF_LOG O141: `T` masquerades through its
first `A − k` moments as a *fiber-like object of stride `A − B`*, and the bad scalar reads
off the pivot coefficient. The KKH26 fiber construction `(X^{rm}, X^{(r−1)m})` is the
special case where a union of `x ↦ x^m`-fibers satisfies every off-stride constraint
structurally (`p_j = 0` for `m ∤ j`); the adjacent-pair laws are the case `A − B = 1`.
Probe ground truth: the (12,6) monomial scan ((9,6) → 4, (10,7) → 4, (11,8) → 4,
(9,8) → 12, others 0) matches this law's censuses where the agreement threshold equals `A`.

## References
* Issue #357, DISPROOF_LOG O138–O141; [KKH26] ePrint 2026/782.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The agreement set of the two-monomial line word `x ↦ x^A + λ·x^B` with the
polynomial `q`, inside the evaluation set `H`. -/
def gapAgreeSet (H : Finset F) (A B : ℕ) (lam : F) (q : Polynomial F) : Finset F :=
  H.filter (fun x => x ^ A + lam * x ^ B = q.eval x)

/-- The line-minus-explanation polynomial `X^A + λ·X^B − q`. -/
noncomputable def gapPoly (A B : ℕ) (lam : F) (q : Polynomial F) : Polynomial F :=
  X ^ A + C lam * X ^ B - q

/-- The full band-and-pivot condition on the vanishing polynomial of `T`:
zero off-pivot coefficients in the band `[k, A − 1]`, pivot value `λ` at degree `B`. -/
def GapBand (T : Finset F) (A B k : ℕ) (lam : F) : Prop :=
  (∀ m, k ≤ m → m < A → m ≠ B → (∏ x ∈ T, (X - C x)).coeff m = 0) ∧
    (∏ x ∈ T, (X - C x)).coeff B = lam

theorem gapPoly_monic {A B k : ℕ} (hk : 1 ≤ k) (hBA : B < A) (hkB : k ≤ B) (lam : F)
    {q : Polynomial F} (hq : q.natDegree ≤ k - 1) :
    (gapPoly A B lam q).Monic ∧ (gapPoly A B lam q).natDegree = A := by
  have htail : (C lam * X ^ B - q).natDegree ≤ B := by
    refine le_trans (natDegree_sub_le _ _) ?_
    refine max_le ?_ (by omega)
    calc (C lam * X ^ B).natDegree ≤ (C lam).natDegree + (X ^ B : Polynomial F).natDegree :=
          natDegree_mul_le
      _ ≤ B := by simp [natDegree_C]
  have hform : gapPoly A B lam q = X ^ A + (C lam * X ^ B - q) := by
    unfold gapPoly; ring
  have hdegtail : (C lam * X ^ B - q).degree < (X ^ A : Polynomial F).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast lt_of_le_of_lt htail hBA)
  have hdegsum : (X ^ A + (C lam * X ^ B - q)).degree = ((A : ℕ) : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt hdegtail, degree_X_pow]
  constructor
  · rw [hform]
    exact (monic_X_pow A).add_of_left hdegtail
  · rw [hform]
    exact natDegree_eq_of_degree_eq_some hdegsum

theorem isRoot_gapPoly_of_mem_agree {H : Finset F} {A B : ℕ} {lam : F} {q : Polynomial F}
    {x : F} (hx : x ∈ gapAgreeSet H A B lam q) :
    (gapPoly A B lam q).IsRoot x := by
  obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
  simp only [IsRoot.def, gapPoly, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  rw [sub_eq_zero]
  exact hx

/-- The agreement set of a bad scalar has size at most `A`. -/
theorem gap_agreement_card_le {H : Finset F} {A B k : ℕ}
    (hk : 1 ≤ k) (hBA : B < A) (hkB : k ≤ B) (lam : F)
    {q : Polynomial F} (hq : q.natDegree ≤ k - 1) :
    (gapAgreeSet H A B lam q).card ≤ A := by
  obtain ⟨hmonic, hdeg⟩ := gapPoly_monic hk hBA hkB lam hq
  have hne : gapPoly A B lam q ≠ 0 := hmonic.ne_zero
  have hsub : gapAgreeSet H A B lam q ⊆ (gapPoly A B lam q).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hne]
    exact isRoot_gapPoly_of_mem_agree hx
  calc (gapAgreeSet H A B lam q).card
      ≤ (gapPoly A B lam q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (gapPoly A B lam q).roots := Multiset.toFinset_card_le _
    _ ≤ (gapPoly A B lam q).natDegree := (gapPoly A B lam q).card_roots'
    _ = A := hdeg

/-- **Forward half: a bad scalar yields a band-constrained `A`-subset with pivot `λ`.** -/
theorem gapBand_of_badScalar {H : Finset F} {A B k : ℕ}
    (hk : 1 ≤ k) (hBA : B < A) (hkB : k ≤ B) {lam : F}
    {q : Polynomial F} (hq : q.natDegree ≤ k - 1)
    (hagree : A ≤ (gapAgreeSet H A B lam q).card) :
    ∃ T ⊆ H, T.card = A ∧ GapBand T A B k lam := by
  classical
  obtain ⟨hmonic, hdeg⟩ := gapPoly_monic hk hBA hkB lam hq
  set T : Finset F := gapAgreeSet H A B lam q with hT
  have hTH : T ⊆ H := Finset.filter_subset _ _
  have hTcard : T.card = A := le_antisymm (gap_agreement_card_le hk hBA hkB lam hq) hagree
  set Q : Polynomial F := ∏ x ∈ T, (X - C x) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c
  have hQdeg : Q.natDegree = A := by
    rw [hQ, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hTcard]
  have hPQ : gapPoly A B lam q = Q := by
    by_contra hne
    have hsubne : gapPoly A B lam q - Q ≠ 0 := sub_ne_zero.mpr hne
    have hroots : ∀ x ∈ T, (gapPoly A B lam q - Q).IsRoot x := by
      intro x hx
      have h1 : (gapPoly A B lam q).IsRoot x := isRoot_gapPoly_of_mem_agree hx
      have h2 : Q.IsRoot x := by
        rw [hQ]
        simp only [IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
        exact Finset.prod_eq_zero hx (by ring)
      simp only [IsRoot.def, eval_sub] at h1 h2 ⊢
      rw [h1, h2, sub_zero]
    have hdegsub : (gapPoly A B lam q - Q).natDegree < A := by
      have hcoeffr : (gapPoly A B lam q - Q).coeff A = 0 := by
        rw [coeff_sub]
        have h1 : (gapPoly A B lam q).coeff A = 1 := by
          have := hmonic.coeff_natDegree
          rwa [hdeg] at this
        have h2 : Q.coeff A = 1 := by
          have := hQmonic.coeff_natDegree
          rwa [hQdeg] at this
        rw [h1, h2, sub_self]
      have hdegle : (gapPoly A B lam q - Q).natDegree ≤ A := by
        refine le_trans (natDegree_sub_le _ _) ?_
        rw [hdeg, hQdeg]; simp
      rcases lt_or_eq_of_le hdegle with h | h
      · exact h
      · exfalso
        have hlc : (gapPoly A B lam q - Q).leadingCoeff = 0 := by
          rw [leadingCoeff, h, hcoeffr]
        exact hsubne (leadingCoeff_eq_zero.mp hlc)
    have hsubroots : T ⊆ (gapPoly A B lam q - Q).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hsubne]
      exact hroots x hx
    have : A ≤ (gapPoly A B lam q - Q).natDegree := by
      calc A = T.card := hTcard.symm
        _ ≤ (gapPoly A B lam q - Q).roots.toFinset.card := Finset.card_le_card hsubroots
        _ ≤ Multiset.card (gapPoly A B lam q - Q).roots := Multiset.toFinset_card_le _
        _ ≤ (gapPoly A B lam q - Q).natDegree := (gapPoly A B lam q - Q).card_roots'
    omega
  refine ⟨T, hTH, hTcard, ?_, ?_⟩
  · -- Off-pivot band coefficients vanish.
    intro m hkm hmA hmB
    rw [← hQ, ← hPQ]
    unfold gapPoly
    have hxa : (X ^ A : Polynomial F).coeff m = 0 := by
      rw [coeff_X_pow]
      simp [show ¬ m = A by omega]
    have hxb : (X ^ B : Polynomial F).coeff m = 0 := by
      rw [coeff_X_pow]
      simp [hmB]
    have hqc : q.coeff m = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < m)
    rw [coeff_sub, coeff_add, coeff_C_mul, hxa, hxb, hqc]
    ring
  · -- The pivot coefficient reads off `λ`.
    rw [← hQ, ← hPQ]
    unfold gapPoly
    have hxa : (X ^ A : Polynomial F).coeff B = 0 := by
      rw [coeff_X_pow]
      simp [show ¬ B = A by omega]
    have hxb : (X ^ B : Polynomial F).coeff B = 1 := by
      rw [coeff_X_pow]
      simp
    have hqc : q.coeff B = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < B)
    rw [coeff_sub, coeff_add, coeff_C_mul, hxa, hxb, hqc]
    ring

/-- **Backward half: every band-constrained `A`-subset realizes its pivot as a bad
scalar.** The explaining polynomial is `q := X^A + λX^B − ∏_T(X − x)`. -/
theorem badScalar_of_gapBand {H : Finset F} {A B k : ℕ}
    (hk : 1 ≤ k) (hBA : B < A) (hkB : k ≤ B) {lam : F}
    {T : Finset F} (hTH : T ⊆ H) (hTcard : T.card = A)
    (hband : GapBand T A B k lam) :
    ∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧
      A ≤ (gapAgreeSet H A B lam q).card := by
  classical
  obtain ⟨hband0, hpivot⟩ := hband
  set Q : Polynomial F := ∏ x ∈ T, (X - C x) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c
  have hQdeg : Q.natDegree = A := by
    rw [hQ, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hTcard]
  have hQa : Q.coeff A = 1 := by
    have := hQmonic.coeff_natDegree
    rwa [hQdeg] at this
  set q : Polynomial F := X ^ A + C lam * X ^ B - Q with hq
  have hqdeg : q.natDegree ≤ k - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hmk : k ≤ m := by omega
    rw [hq, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X_pow]
    rcases Nat.lt_or_ge A m with hcase | hcase
    · -- `m > A`.
      have hQm : Q.coeff m = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m)
      simp [show ¬ m = A by omega, show ¬ m = B by omega, hQm]
    · rcases Nat.eq_or_lt_of_le hcase with heq | hlt
      · -- `m = A`.
        rw [heq]
        simp [show ¬ A = B by omega, hQa]
      · rcases eq_or_ne m B with heqB | hneB
        · -- `m = B`: the pivot cancels.
          rw [heqB]
          simp [show ¬ B = A by omega, hpivot]
        · -- off-pivot band: `k ≤ m < A`, `m ≠ B`.
          have hband' : Q.coeff m = 0 := hband0 m hmk hlt hneB
          simp [show ¬ m = A by omega, hneB, hband']
  refine ⟨q, hqdeg, ?_⟩
  have hsub : T ⊆ gapAgreeSet H A B lam q := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨hTH hx, ?_⟩
    have hQx : Q.eval x = 0 := by
      rw [hQ]
      simp only [eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero hx (by ring)
    rw [hq]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, hQx]
    ring
  calc A = T.card := hTcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **THE GAP CENSUS LAW (arbitrary two-monomial stack).** Against polynomials of degree
`< k` over any finite evaluation set in any field, the bad scalars of `(X^A, X^B)`
(`k ≤ B < A`) at agreement threshold `A` are exactly the pivot coefficients of the
band-constrained `A`-subsets. The adjacent-pair laws are the case `B = A − 1`; the KKH26
fiber stacks are `(A, B) = (rm, (r−1)m)`, where fiber unions satisfy the off-stride band
structurally. -/
theorem badScalar_iff_gapBand (H : Finset F) {A B k : ℕ}
    (hk : 1 ≤ k) (hBA : B < A) (hkB : k ≤ B) (lam : F) :
    (∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧ A ≤ (gapAgreeSet H A B lam q).card) ↔
      (∃ T ⊆ H, T.card = A ∧ GapBand T A B k lam) := by
  constructor
  · rintro ⟨q, hq, hagree⟩
    exact gapBand_of_badScalar hk hBA hkB hq hagree
  · rintro ⟨T, hTH, hTcard, hband⟩
    exact badScalar_of_gapBand hk hBA hkB hTH hTcard hband

/-! ## Source audit -/

#print axioms gapBand_of_badScalar
#print axioms badScalar_of_gapBand
#print axioms badScalar_iff_gapBand

end ArkLib.ProximityGap.KKH26
