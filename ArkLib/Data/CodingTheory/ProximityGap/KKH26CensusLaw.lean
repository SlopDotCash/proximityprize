/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26BadLineConstruction

/-!
# The exact census law for the KKH26 monomial-pair line (m = 1)

The [KKH26] bad-line construction (`kkh26_badline_closePoints`) produces, for each
antipodal-free `r`-subset sum, a close point of the line `{X^r + λ·X^{r−1}}` — a **lower
bound** on the bad-scalar census. The in-tree stratified spread (`KKH26StratifiedSpread`)
enlarges the produced family. This file proves the **exact law** (probe-discovered, two
scales of exact set-equality evidence — `scripts/probes/probe_r2b_stratified_census_exact.py`,
DISPROOF_LOG O136):

  for any finite evaluation set `H` in any field and any `r ≥ 2`, a scalar `λ` is bad at
  agreement threshold `r` (the line word `x ↦ x^r + λ·x^{r−1}` agrees with some polynomial of
  degree `≤ r − 2` on at least `r` points of `H`) **iff** `λ = −∑ T` for some `r`-subset
  `T ⊆ H`.

So the bad-scalar set is *exactly* `{−∑ T : T ∈ C(H, r)}` — the construction side
(`badScalar_of_subsetSum`, from `gap_expansion` at `m = 1`) and the new converse
(`subsetSum_of_badScalar`): the difference `X^r + λX^{r−1} − q` is **monic of degree exactly
`r`**, so `≥ r` agreements force *exactly* `r` roots, the agreement set `T` is pinned, the
polynomial factors as `∏_{x∈T}(X − x)`, and the `X^{r−1}` coefficient (Vieta) pins
`λ = −∑ T`. Three structural consequences:

* the census is **domain-agnostic** — the multiplicative-subgroup structure of `H` enters
  only when *counting distinct* subset sums (which is exactly what `kkh26_lemma1` and the
  stratified spread do);
* the KKH26 ceiling numerator upgrades from "≥ the constructed family" to "= the number of
  distinct `r`-subset sums" — the stratified count is census-exact whenever it is
  sum-injective;
* the agreement structure is rigid: a bad scalar's agreement set is *unique* and has size
  exactly `r` (`agreement_card_eq`), and the explaining polynomial is determined.

## References

* [KKH26] ePrint 2026/782; issue #357 (R2/S1 lanes), DISPROOF_LOG O136.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The agreement set of the line word `x ↦ x^r + λ·x^{r−1}` with the polynomial `q`,
inside the evaluation set `H`. -/
def lineAgreeSet (H : Finset F) (r : ℕ) (lam : F) (q : Polynomial F) : Finset F :=
  H.filter (fun x => x ^ r + lam * x ^ (r - 1) = q.eval x)

/-- The line-minus-explanation polynomial `X^r + λ·X^{r−1} − q`. -/
noncomputable def linePoly (r : ℕ) (lam : F) (q : Polynomial F) : Polynomial F :=
  X ^ r + C lam * X ^ (r - 1) - q

omit [DecidableEq F] in
theorem linePoly_tail_natDegree_le {r : ℕ} (hr2 : 2 ≤ r) (lam : F)
    {q : Polynomial F} (hq : q.natDegree ≤ r - 2) :
    (C lam * X ^ (r - 1) - q).natDegree ≤ r - 1 := by
  refine le_trans (natDegree_sub_le _ _) ?_
  refine max_le ?_ (le_trans hq (by omega))
  calc (C lam * X ^ (r - 1)).natDegree ≤ (C lam).natDegree + (X ^ (r - 1)).natDegree :=
        natDegree_mul_le
    _ ≤ r - 1 := by simp [natDegree_C]

omit [DecidableEq F] in
/-- `linePoly` is monic of degree exactly `r`. -/
theorem linePoly_monic {r : ℕ} (hr2 : 2 ≤ r) (lam : F)
    {q : Polynomial F} (hq : q.natDegree ≤ r - 2) :
    (linePoly r lam q).Monic ∧ (linePoly r lam q).natDegree = r := by
  have htail := linePoly_tail_natDegree_le hr2 lam hq
  have hform : linePoly r lam q = X ^ r + (C lam * X ^ (r - 1) - q) := by
    unfold linePoly; ring
  have hnatlt : (C lam * X ^ (r - 1) - q).natDegree < r := by omega
  have hdegtail : (C lam * X ^ (r - 1) - q).degree < (X ^ r : Polynomial F).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hnatlt)
  have hdegsum : (X ^ r + (C lam * X ^ (r - 1) - q)).degree = ((r : ℕ) : WithBot ℕ) := by
    rw [degree_add_eq_left_of_degree_lt hdegtail, degree_X_pow]
  constructor
  · rw [hform]
    exact (monic_X_pow r).add_of_left hdegtail
  · rw [hform]
    exact natDegree_eq_of_degree_eq_some hdegsum

/-- Every point of the agreement set is a root of `linePoly`. -/
theorem isRoot_linePoly_of_mem_agree {H : Finset F} {r : ℕ} {lam : F} {q : Polynomial F}
    {x : F} (hx : x ∈ lineAgreeSet H r lam q) :
    (linePoly r lam q).IsRoot x := by
  obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
  simp only [IsRoot.def, linePoly, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  rw [sub_eq_zero]
  exact hx

/-- **Rigidity: the agreement set of a bad scalar has size at most `r`.** The difference is
monic of degree exactly `r`, hence has at most `r` roots. -/
theorem agreement_card_le {H : Finset F} {r : ℕ} (hr2 : 2 ≤ r) (lam : F)
    {q : Polynomial F} (hq : q.natDegree ≤ r - 2) :
    (lineAgreeSet H r lam q).card ≤ r := by
  obtain ⟨hmonic, hdeg⟩ := linePoly_monic hr2 lam hq
  have hne : linePoly r lam q ≠ 0 := hmonic.ne_zero
  have hsub : lineAgreeSet H r lam q ⊆ (linePoly r lam q).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hne]
    exact isRoot_linePoly_of_mem_agree hx
  calc (lineAgreeSet H r lam q).card
      ≤ (linePoly r lam q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (linePoly r lam q).roots := Multiset.toFinset_card_le _
    _ ≤ (linePoly r lam q).natDegree := (linePoly r lam q).card_roots'
    _ = r := hdeg

/-- **The forward half (the new converse): a bad scalar is an `r`-subset sum.** If the line
word agrees with some degree-`≤ r−2` polynomial on `≥ r` points of `H`, then the agreement
set has size exactly `r`, `linePoly` splits over it, and Vieta pins `λ = −∑ T`. -/
theorem subsetSum_of_badScalar {H : Finset F} {r : ℕ} (hr2 : 2 ≤ r) {lam : F}
    {q : Polynomial F} (hq : q.natDegree ≤ r - 2)
    (hagree : r ≤ (lineAgreeSet H r lam q).card) :
    ∃ T ⊆ H, T.card = r ∧ lam = -∑ a ∈ T, a := by
  classical
  obtain ⟨hmonic, hdeg⟩ := linePoly_monic hr2 lam hq
  set T : Finset F := lineAgreeSet H r lam q with hT
  have hTH : T ⊆ H := Finset.filter_subset _ _
  have hTcard : T.card = r := le_antisymm (agreement_card_le hr2 lam hq) hagree
  refine ⟨T, hTH, hTcard, ?_⟩
  -- `linePoly = ∏_{x∈T}(X − x)`: both monic of degree `r`, difference vanishes on `T`.
  set Q : Polynomial F := ∏ x ∈ T, (X - C x) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  have hQdeg : Q.natDegree = r := by
    rw [hQ, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C a]
    simp [hTcard]
  have hPQ : linePoly r lam q = Q := by
    by_contra hne
    have hsubne : linePoly r lam q - Q ≠ 0 := sub_ne_zero.mpr hne
    have hroots : ∀ x ∈ T, (linePoly r lam q - Q).IsRoot x := by
      intro x hx
      have h1 : (linePoly r lam q).IsRoot x := isRoot_linePoly_of_mem_agree hx
      have h2 : Q.IsRoot x := by
        rw [hQ]
        simp only [IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
        exact Finset.prod_eq_zero hx (by ring)
      simp only [IsRoot.def, eval_sub] at h1 h2 ⊢
      rw [h1, h2, sub_zero]
    have hdegsub : (linePoly r lam q - Q).natDegree < r := by
      have hcoeffr : (linePoly r lam q - Q).coeff r = 0 := by
        rw [coeff_sub]
        have h1 : (linePoly r lam q).coeff r = 1 := by
          have := hmonic.coeff_natDegree
          rwa [hdeg] at this
        have h2 : Q.coeff r = 1 := by
          have := hQmonic.coeff_natDegree
          rwa [hQdeg] at this
        rw [h1, h2, sub_self]
      have hdegle : (linePoly r lam q - Q).natDegree ≤ r := by
        refine le_trans (natDegree_sub_le _ _) ?_
        rw [hdeg, hQdeg]; simp
      rcases lt_or_eq_of_le hdegle with h | h
      · exact h
      · exfalso
        have hlc : (linePoly r lam q - Q).leadingCoeff = 0 := by
          rw [leadingCoeff, h, hcoeffr]
        exact hsubne (leadingCoeff_eq_zero.mp hlc)
    -- A nonzero polynomial of degree `< r` cannot vanish on the `r`-point set `T`.
    have hsubroots : T ⊆ (linePoly r lam q - Q).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hsubne]
      exact hroots x hx
    have : r ≤ (linePoly r lam q - Q).natDegree := by
      calc r = T.card := hTcard.symm
        _ ≤ (linePoly r lam q - Q).roots.toFinset.card := Finset.card_le_card hsubroots
        _ ≤ Multiset.card (linePoly r lam q - Q).roots := Multiset.toFinset_card_le _
        _ ≤ (linePoly r lam q - Q).natDegree := (linePoly r lam q - Q).card_roots'
    omega
  -- Vieta at the `X^{r−1}` coefficient.
  have hlhs : (linePoly r lam q).coeff (r - 1) = lam := by
    unfold linePoly
    have h2 : q.coeff (r - 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < r - 1)
    have hxr : (X ^ r : Polynomial F).coeff (r - 1) = 0 := by
      rw [coeff_X_pow]
      simp [show ¬ r - 1 = r by omega]
    have hxr1 : (X ^ (r - 1) : Polynomial F).coeff (r - 1) = 1 := by
      rw [coeff_X_pow]
      simp
    rw [coeff_sub, coeff_add, coeff_C_mul, hxr, hxr1, h2]
    ring
  have hrhs : Q.coeff (r - 1) = -∑ a ∈ T, a := by
    have h1 : Q.nextCoeff = -∑ a ∈ T, a := by
      rw [hQ]
      exact prod_X_sub_C_nextCoeff (fun a => a)
    have h2 : Q.nextCoeff = Q.coeff (Q.natDegree - 1) :=
      nextCoeff_of_natDegree_pos (by rw [hQdeg]; omega)
    rw [h2, hQdeg] at h1
    exact h1
  rw [hPQ, hrhs] at hlhs
  exact hlhs.symm

/-- **The backward half (the construction): every `r`-subset sum is a bad scalar.**
From `gap_expansion` at `m = 1`: with `λ = −∑ T`, the polynomial `q := −E` of degree
`≤ r − 2` agrees with the line word on all of `T`. -/
theorem badScalar_of_subsetSum {H : Finset F} {r : ℕ} (hr2 : 2 ≤ r)
    {T : Finset F} (hTH : T ⊆ H) (hTcard : T.card = r) :
    ∃ q : Polynomial F, q.natDegree ≤ r - 2 ∧
      r ≤ (lineAgreeSet H r (-∑ a ∈ T, a) q).card := by
  classical
  obtain ⟨E, hEeq, hEdeg⟩ := gap_expansion T (le_refl 1) (by omega)
  rw [hTcard] at hEeq hEdeg
  refine ⟨-E, by simpa using hEdeg, ?_⟩
  have hsub : T ⊆ lineAgreeSet H r (-∑ a ∈ T, a) (-E) := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨hTH hx, ?_⟩
    have heval := congrArg (Polynomial.eval x) hEeq
    rw [eval_prod] at heval
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at heval
    have hvanish : (∏ a ∈ T, (x ^ 1 - a)) = 0 :=
      Finset.prod_eq_zero hx (by ring)
    rw [hvanish] at heval
    simp only [mul_one] at heval
    rw [eval_neg]
    linear_combination -heval
  calc r = T.card := hTcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **THE CENSUS LAW (m = 1, domain-agnostic).** A scalar is bad for the monomial-pair line
`(X^r, X^{r−1})` at agreement threshold `r` over any finite evaluation set `H` **iff** it is
the negated sum of an `r`-subset of `H`:

  `{λ | bad} = {−∑ T : T ∈ C(H, r)}`.

The KKH26/stratified constructions are therefore census-exact: the bad-scalar count *equals*
the number of distinct `r`-subset sums. (Probe ground truth: 41 = 41 at `(p,μ,r) = (4129,3,4)`
and 5 = 5 at the folded scale, every β.) -/
theorem badScalar_iff_subsetSum (H : Finset F) {r : ℕ} (hr2 : 2 ≤ r) (lam : F) :
    (∃ q : Polynomial F, q.natDegree ≤ r - 2 ∧ r ≤ (lineAgreeSet H r lam q).card) ↔
      lam ∈ (H.powersetCard r).image (fun T => -∑ a ∈ T, a) := by
  constructor
  · rintro ⟨q, hq, hagree⟩
    obtain ⟨T, hTH, hTcard, rfl⟩ := subsetSum_of_badScalar hr2 hq hagree
    exact Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨hTH, hTcard⟩, rfl⟩
  · intro hlam
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hlam
    obtain ⟨hTH, hTcard⟩ := Finset.mem_powersetCard.mp hT
    exact badScalar_of_subsetSum hr2 hTH hTcard

open Classical in
/-- **The census count.** The number of bad scalars equals the number of distinct `r`-subset
sums of the domain — the object that `kkh26_lemma1` (antipodal-free subsets) and the
stratified spread lower-bound, now exactly. -/
theorem badScalar_census_card [Fintype F] (H : Finset F) {r : ℕ} (hr2 : 2 ≤ r) :
    (Finset.univ.filter (fun lam : F =>
        ∃ q : Polynomial F, q.natDegree ≤ r - 2 ∧
          r ≤ (lineAgreeSet H r lam q).card)).card =
      ((H.powersetCard r).image (fun T => -∑ a ∈ T, a)).card := by
  apply congrArg Finset.card
  ext lam
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact badScalar_iff_subsetSum H hr2 lam

/-! ## Source audit -/

#print axioms subsetSum_of_badScalar
#print axioms badScalar_of_subsetSum
#print axioms badScalar_iff_subsetSum
#print axioms badScalar_census_card

end ArkLib.ProximityGap.KKH26
