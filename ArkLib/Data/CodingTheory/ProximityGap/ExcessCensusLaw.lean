/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ConstrainedCensusLaw

/-!
# The excess census law: the corrected upper-side object after the take-over

The take-over countermodel (`TakeoverCountermodel.lean`) killed the agreement-matched
census as the extremality surface: at agreement `a`, the worst monomial pair is *not*
`(X^a, X^{a−1})` but `(X^s, X^{s−1})` for `s > a` — the vanishing polynomial has degree
`s` with only `a` roots pinned in the domain and `s − a` roots free. This file proves the
**exact law for the corrected object**, at every degree excess:

`monomial_badScalar_iff_excess` — for any finite `H` in any field, any `1 ≤ k`,
`k + 1 ≤ a ≤ s`: the scalar `λ` is bad for the pair `(X^s, X^{s−1})` at agreement `≥ a`
(i.e. the line agrees with some degree-`< k` polynomial on `≥ a` points of `H`) **iff**
there is an `a`-subset `T ⊆ H` and a *monic cofactor* `gq` of degree `s − a` such that
the product `P = V_T · gq` (with `V_T` the vanishing polynomial of `T`) has

* zero coefficients across the excess band `k ≤ j ≤ s − 2`, and
* `coeff_{s−1}(P) = λ`.

The agreement-matched constrained census law (`badScalar_iff_constrainedSubsetSum`) is
exactly the `s = a` slice (`gq = 1` forced). The take-over at `(16,4)`, `a = 7` is the
`s = 9` slice — `V_T` of seven domain points times a linear free factor. The free factor
ranges over *monic polynomials*, not free roots: over a non-closed field the excess mass
need not split, which is precisely where the measured field-dependence (Weil regime past
Johnson) enters the census and where the agreement-matched object went blind.

**Position in the programme.** This is the per-`(s, a)` slice law. The corrected
upper-extremality surface for the δ\*-pin is now: *the worst stack at agreement `a` is
bounded by the union over `s ≥ a` of excess-census slices* — with this law, that surface
is a statement about explicit polynomial families only, and every slice is
machine-checkable per instance. The slice-census cardinality theory (how the free factor
count interacts with the band system — the analytic core) is the open follow-up.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (the take-over arc and corrected target); `KKH26ConstrainedCensusLaw.lean`
  (the `s = a` slice), `TakeoverCountermodel.lean` (the `s = 9 > a = 7` instance).
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.ExcessCensus

open Polynomial Finset
open ArkLib.ProximityGap.KKH26

variable {F : Type*} [Field F] [DecidableEq F]

/-- The vanishing polynomial of a finite set. -/
noncomputable def vanish (T : Finset F) : Polynomial F := ∏ x ∈ T, (X - C x)

theorem vanish_monic (T : Finset F) : (vanish T).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

theorem vanish_natDegree (T : Finset F) : (vanish T).natDegree = T.card := by
  unfold vanish
  rw [natDegree_prod _ _ fun x _ => X_sub_C_ne_zero x]
  simp [natDegree_X_sub_C]

theorem vanish_eval_zero {T : Finset F} {x : F} (hx : x ∈ T) :
    (vanish T).eval x = 0 := by
  unfold vanish
  rw [eval_prod]
  exact Finset.prod_eq_zero hx (by simp)

/-- **The excess witness:** an `a`-subset of the domain together with a monic cofactor
of degree `s − a`, whose product has zero excess band and `λ` at the subleading
coefficient. -/
def ExcessWitness (H : Finset F) (k s a : ℕ) (lam : F) : Prop :=
  ∃ T ⊆ H, T.card = a ∧ ∃ gq : Polynomial F, gq.Monic ∧ gq.natDegree = s - a ∧
    (∀ j, k ≤ j → j ≤ s - 2 → (vanish T * gq).coeff j = 0) ∧
    (vanish T * gq).coeff (s - 1) = lam

/-! ## Forward: a bad scalar yields an excess witness -/

theorem excessWitness_of_badScalar {H : Finset F} {k s a : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (has : a ≤ s) {lam : F}
    {q : Polynomial F} (hq : q.natDegree ≤ k - 1)
    (hagree : a ≤ (lineAgreeSet H s lam q).card) :
    ExcessWitness H k s a lam := by
  classical
  have hs2 : 2 ≤ s := by omega
  have hq' : q.natDegree ≤ s - 2 := by omega
  obtain ⟨hmonic, hdeg⟩ := linePoly_monic hs2 lam hq'
  have hne : linePoly s lam q ≠ 0 := hmonic.ne_zero
  -- pick an a-subset of the agreement set
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hagree
  have hTH : T ⊆ H := hTsub.trans (Finset.filter_subset _ _)
  -- T's vanishing polynomial divides linePoly
  have hdvd : vanish T ∣ linePoly s lam q := by
    have hle : T.val ≤ (linePoly s lam q).roots := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x ∈ T
      · have hroot : (linePoly s lam q).IsRoot x :=
          isRoot_linePoly_of_mem_agree (hTsub hx)
        have hcount : T.val.count x = 1 :=
          Multiset.count_eq_one_of_mem T.nodup hx
        rw [hcount, count_roots]
        exact (Polynomial.rootMultiplicity_pos hne).mpr hroot
      · have hcount : T.val.count x = 0 := by
          rw [Multiset.count_eq_zero]
          exact hx
        rw [hcount]
        exact Nat.zero_le _
    have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hne T.val).mpr hle
    unfold vanish
    rw [Finset.prod_eq_multiset_prod]
    exact this
  obtain ⟨gq, hgq⟩ := hdvd
  have hVne : vanish T ≠ 0 := (vanish_monic T).ne_zero
  have hgq_monic : gq.Monic := by
    have hprod_monic : (vanish T * gq).Monic := hgq ▸ hmonic
    exact (vanish_monic T).of_mul_monic_left hprod_monic
  have hgq_deg : gq.natDegree = s - a := by
    have hdegs : (vanish T * gq).natDegree = s := by rw [← hgq, hdeg]
    rw [natDegree_mul hVne hgq_monic.ne_zero, vanish_natDegree, hTcard] at hdegs
    omega
  refine ⟨T, hTH, hTcard, gq, hgq_monic, hgq_deg, ?_, ?_⟩
  · -- the excess band of linePoly vanishes
    intro j hjk hjs
    rw [← hgq]
    unfold linePoly
    rw [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_pow]
    have hjq : q.coeff j = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      omega
    have hjs' : j ≠ s := by omega
    have hjs1 : j ≠ s - 1 := by omega
    simp [hjs', hjs1, hjq]
  · -- the subleading coefficient is λ
    rw [← hgq]
    unfold linePoly
    rw [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_pow]
    have hq1 : q.coeff (s - 1) = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      omega
    have hne1 : s - 1 ≠ s := by omega
    simp [hne1, hq1]

/-! ## Backward: an excess witness yields a bad scalar -/

theorem badScalar_of_excessWitness {H : Finset F} {k s a : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (has : a ≤ s) {lam : F}
    (hw : ExcessWitness H k s a lam) :
    ∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧ a ≤ (lineAgreeSet H s lam q).card := by
  classical
  obtain ⟨T, hTH, hTcard, gq, hgq_monic, hgq_deg, hband, hsub1⟩ := hw
  set P : Polynomial F := vanish T * gq with hP
  have hP_monic : P.Monic := (vanish_monic T).mul hgq_monic
  have hP_deg : P.natDegree = s := by
    rw [hP, natDegree_mul (vanish_monic T).ne_zero hgq_monic.ne_zero,
      vanish_natDegree, hTcard, hgq_deg]
    omega
  have hs2 : 2 ≤ s := by omega
  -- the explanation polynomial
  set q : Polynomial F := X ^ s + C lam * X ^ (s - 1) - P with hq_def
  have hq_coeff : ∀ j, k ≤ j → q.coeff j = 0 := by
    intro j hjk
    rw [hq_def, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_pow]
    rcases lt_trichotomy j s with hjs | hjs | hjs
    · rcases Nat.lt_or_ge j (s - 1) with hj1 | hj1
      · -- the excess band k ≤ j ≤ s − 2
        have hje : j ≤ s - 2 := by omega
        have hjne : j ≠ s := by omega
        have hjne1 : j ≠ s - 1 := by omega
        have hPj : P.coeff j = 0 := hband j hjk hje
        simp [hjne, hjne1, hPj]
      · -- j = s − 1: the subleading coefficient
        have hje : j = s - 1 := by omega
        have hjne : j ≠ s := by omega
        subst hje
        simp only [if_neg hjne, if_pos, hsub1]
        simp
    · -- j = s: leading coefficients cancel
      subst hjs
      have hne1 : j ≠ j - 1 := by omega
      have hPs : P.coeff j = 1 := by
        have := hP_monic
        rw [Polynomial.Monic, Polynomial.leadingCoeff, hP_deg] at this
        exact this
      simp [hne1, hPs]
    · -- j > s: everything above the degree vanishes
      have hjne : j ≠ s := by omega
      have hjne1 : j ≠ s - 1 := by omega
      have hPj : P.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hjne, hjne1, hPj]
  have hq_deg : q.natDegree ≤ k - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    exact hq_coeff m (by omega)
  refine ⟨q, hq_deg, ?_⟩
  have hTagree : T ⊆ lineAgreeSet H s lam q := by
    intro x hx
    rw [lineAgreeSet, Finset.mem_filter]
    refine ⟨hTH hx, ?_⟩
    have hPx : P.eval x = 0 := by
      rw [hP, eval_mul, vanish_eval_zero hx, zero_mul]
    rw [hq_def]
    simp [eval_sub, eval_add, eval_mul, eval_pow, hPx]
  calc a = T.card := hTcard.symm
    _ ≤ _ := Finset.card_le_card hTagree

/-! ## The law -/

/-- **THE EXCESS CENSUS LAW.** Against polynomials of degree `< k` over any finite `H` in
any field, the bad scalars of the degree-excess monomial pair `(X^s, X^{s−1})` at
agreement threshold `a ≤ s` are exactly the excess witnesses: an `a`-subset of `H` whose
vanishing polynomial, times a monic cofactor of degree `s − a`, has zero excess band and
`λ` at the subleading coefficient. The agreement-matched constrained census law is the
`s = a` slice; the `(16,4)` take-over is the `s = 9 > a = 7` slice. -/
theorem monomial_badScalar_iff_excess (H : Finset F) {k s a : ℕ}
    (hk : 1 ≤ k) (hka : k + 1 ≤ a) (has : a ≤ s) (lam : F) :
    (∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧ a ≤ (lineAgreeSet H s lam q).card) ↔
      ExcessWitness H k s a lam := by
  constructor
  · rintro ⟨q, hq, hagree⟩
    exact excessWitness_of_badScalar hk hka has hq hagree
  · intro hw
    exact badScalar_of_excessWitness hk hka has hw

/-! ## Source audit -/

#print axioms excessWitness_of_badScalar
#print axioms badScalar_of_excessWitness
#print axioms monomial_badScalar_iff_excess

end ArkLib.ProximityGap.ExcessCensus
