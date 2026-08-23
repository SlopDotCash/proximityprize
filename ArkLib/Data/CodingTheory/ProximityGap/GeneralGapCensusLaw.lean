/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExcessCensusLaw

/-!
# The general-gap census law: arbitrary monomial pairs `(X^s, X^t)`

The excess census law (`ExcessCensusLaw.lean`) covers adjacent pairs `(X^s, X^{s−1})`.
But the middle-band probes' worst pairs are **not adjacent**: at `(16,4)`, agreement 6,
the maximizers are `(X¹⁰, X⁷)` and `(X¹⁰, X⁴)` — general gaps. This file proves the law
for **every** monomial pair `(X^s, X^t)` with `k ≤ t < s`:

`gap_badScalar_iff_excess` — `λ` is bad for `(X^s, X^t)` at agreement `≥ a` (against
degree-`< k` explanations on `H`) **iff** there is an `a`-subset `T ⊆ H` and a monic
cofactor `gq` of degree `s − a` with `P = V_T · gq` satisfying

* `P.coeff j = 0` for every `j` in the **punctured band** `k ≤ j ≤ s − 1`, `j ≠ t`, and
* `P.coeff t = λ`.

The adjacent law is the `t = s − 1` case (the puncture absorbs the old subleading slot);
the constrained law is `t = s − 1, s = a`. The hypothesis `k ≤ t` is essential: for
`t < k` the `λX^t` term is absorbable into the explanation and badness degenerates to a
`λ`-independent statement (every scalar or none — the row-codeword regime).

With this, the **entire monomial-stack landscape over any domain is law-governed**: every
probe table entry (adjacent, half-order, general-gap) is the cardinality of one explicit
polynomial family. On `μ_n` the function-level reduction `x^n = 1` caps the relevant
exponents at `s, t < n` — the corrected upper-extremality surface (monomial pairs are
extremal, the standing conjecture after the take-over) now quantifies over a **finite,
fully-characterized** family.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (middle-band cartography); `ExcessCensusLaw.lean` (the adjacent case and
  the `vanish` API), `probe_middle_band_ladder.py` (the non-adjacent maximizers).
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.GeneralGapCensus

open Polynomial Finset
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.ExcessCensus

variable {F : Type*} [Field F] [DecidableEq F]

/-- The agreement set of the general-gap line `x^s + λx^t` against the explanation `q`. -/
def gapAgreeSet (H : Finset F) (s t : ℕ) (lam : F) (q : Polynomial F) : Finset F :=
  H.filter (fun x => x ^ s + lam * x ^ t = q.eval x)

/-- The general-gap line polynomial `X^s + λX^t − q`. -/
noncomputable def gapPoly (s t : ℕ) (lam : F) (q : Polynomial F) : Polynomial F :=
  X ^ s + C lam * X ^ t - q

theorem gapPoly_monic {s t : ℕ} (hts : t < s) (lam : F)
    {q : Polynomial F} (hq : q.natDegree ≤ s - 1) :
    (gapPoly s t lam q).Monic ∧ (gapPoly s t lam q).natDegree = s := by
  have htail : (C lam * X ^ t - q).natDegree ≤ s - 1 := by
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ hq)
    calc (C lam * X ^ t).natDegree ≤ (C lam).natDegree + (X ^ t : Polynomial F).natDegree :=
          natDegree_mul_le
      _ ≤ s - 1 := by simp [natDegree_C, natDegree_X_pow]; omega
  have hform : gapPoly s t lam q = X ^ s + (C lam * X ^ t - q) := by
    unfold gapPoly; ring
  have hs1 : 1 ≤ s := by omega
  have hdegtail : (C lam * X ^ t - q).degree < (X ^ s : Polynomial F).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt degree_le_natDegree ?_
    exact_mod_cast (by omega : (C lam * X ^ t - q).natDegree < s)
  constructor
  · rw [hform]
    exact (monic_X_pow s).add_of_left hdegtail
  · rw [hform]
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_add_eq_left_of_degree_lt hdegtail, degree_X_pow]

theorem isRoot_gapPoly_of_mem {H : Finset F} {s t : ℕ} {lam : F} {q : Polynomial F}
    {x : F} (hx : x ∈ gapAgreeSet H s t lam q) :
    (gapPoly s t lam q).IsRoot x := by
  obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
  simp only [IsRoot.def, gapPoly, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  rw [sub_eq_zero]
  exact hx

/-- **The general-gap excess witness:** the punctured-band condition. -/
def GapWitness (H : Finset F) (k s t a : ℕ) (lam : F) : Prop :=
  ∃ T ⊆ H, T.card = a ∧ ∃ gq : Polynomial F, gq.Monic ∧ gq.natDegree = s - a ∧
    (∀ j, k ≤ j → j ≤ s - 1 → j ≠ t → (vanish T * gq).coeff j = 0) ∧
    (vanish T * gq).coeff t = lam

/-! ## Forward -/

theorem gapWitness_of_badScalar {H : Finset F} {k s t a : ℕ}
    (hk : 1 ≤ k) (hkt : k ≤ t) (hts : t < s) (hka : k + 1 ≤ a) (has : a ≤ s) {lam : F}
    {q : Polynomial F} (hq : q.natDegree ≤ k - 1)
    (hagree : a ≤ (gapAgreeSet H s t lam q).card) :
    GapWitness H k s t a lam := by
  classical
  have hq' : q.natDegree ≤ s - 1 := by omega
  obtain ⟨hmonic, hdeg⟩ := gapPoly_monic hts lam hq'
  have hne : gapPoly s t lam q ≠ 0 := hmonic.ne_zero
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hagree
  have hTH : T ⊆ H := hTsub.trans (Finset.filter_subset _ _)
  have hdvd : vanish T ∣ gapPoly s t lam q := by
    have hle : T.val ≤ (gapPoly s t lam q).roots := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x ∈ T
      · have hroot : (gapPoly s t lam q).IsRoot x :=
          isRoot_gapPoly_of_mem (hTsub hx)
        rw [Multiset.count_eq_one_of_mem T.nodup hx, count_roots]
        exact (Polynomial.rootMultiplicity_pos hne).mpr hroot
      · rw [Multiset.count_eq_zero.mpr hx]
        exact Nat.zero_le _
    have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hne T.val).mpr hle
    unfold vanish
    rw [Finset.prod_eq_multiset_prod]
    exact this
  obtain ⟨gq, hgq⟩ := hdvd
  have hgq_monic : gq.Monic :=
    (vanish_monic T).of_mul_monic_left (hgq ▸ hmonic)
  have hgq_deg : gq.natDegree = s - a := by
    have hdegs : (vanish T * gq).natDegree = s := by rw [← hgq, hdeg]
    rw [natDegree_mul (vanish_monic T).ne_zero hgq_monic.ne_zero,
      vanish_natDegree, hTcard] at hdegs
    omega
  refine ⟨T, hTH, hTcard, gq, hgq_monic, hgq_deg, ?_, ?_⟩
  · intro j hjk hjs hjt
    rw [← hgq]
    unfold gapPoly
    rw [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_pow]
    have hjq : q.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hjs' : j ≠ s := by omega
    simp [hjs', hjt, hjq]
  · rw [← hgq]
    unfold gapPoly
    rw [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_pow]
    have hq1 : q.coeff t = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hne1 : t ≠ s := by omega
    simp [hne1, hq1]

/-! ## Backward -/

theorem badScalar_of_gapWitness {H : Finset F} {k s t a : ℕ}
    (hk : 1 ≤ k) (hkt : k ≤ t) (hts : t < s) (hka : k + 1 ≤ a) (has : a ≤ s) {lam : F}
    (hw : GapWitness H k s t a lam) :
    ∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧ a ≤ (gapAgreeSet H s t lam q).card := by
  classical
  obtain ⟨T, hTH, hTcard, gq, hgq_monic, hgq_deg, hband, hcoefft⟩ := hw
  set P : Polynomial F := vanish T * gq with hP
  have hP_monic : P.Monic := (vanish_monic T).mul hgq_monic
  have hP_deg : P.natDegree = s := by
    rw [hP, natDegree_mul (vanish_monic T).ne_zero hgq_monic.ne_zero,
      vanish_natDegree, hTcard, hgq_deg]
    omega
  set q : Polynomial F := X ^ s + C lam * X ^ t - P with hq_def
  have hq_coeff : ∀ j, k ≤ j → q.coeff j = 0 := by
    intro j hjk
    rw [hq_def, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_pow]
    rcases lt_trichotomy j s with hjs | hjs | hjs
    · by_cases hjt : j = t
      · subst hjt
        have hjne : j ≠ s := by omega
        simp [hjne, hcoefft]
      · have hjne : j ≠ s := by omega
        have hPj : P.coeff j = 0 := hband j hjk (by omega) hjt
        simp [hjne, hjt, hPj]
    · subst hjs
      have hne1 : j ≠ t := by omega
      have hPs : P.coeff j = 1 := by
        have hmon := hP_monic
        rw [Polynomial.Monic, Polynomial.leadingCoeff, hP_deg] at hmon
        exact hmon
      simp [hne1, hPs]
    · have hjne : j ≠ s := by omega
      have hjne1 : j ≠ t := by omega
      have hPj : P.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hjne, hjne1, hPj]
  have hq_deg : q.natDegree ≤ k - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    exact hq_coeff m (by omega)
  refine ⟨q, hq_deg, ?_⟩
  have hTagree : T ⊆ gapAgreeSet H s t lam q := by
    intro x hx
    rw [gapAgreeSet, Finset.mem_filter]
    refine ⟨hTH hx, ?_⟩
    have hPx : P.eval x = 0 := by
      rw [hP, eval_mul, vanish_eval_zero hx, zero_mul]
    rw [hq_def]
    simp [eval_sub, eval_add, eval_mul, eval_pow, hPx]
  calc a = T.card := hTcard.symm
    _ ≤ _ := Finset.card_le_card hTagree

/-! ## The law -/

/-- **THE GENERAL-GAP CENSUS LAW.** For any finite `H` in any field, `1 ≤ k ≤ t < s`,
`k + 1 ≤ a ≤ s`: `λ` is bad for the monomial pair `(X^s, X^t)` at agreement `≥ a` iff
the punctured-band excess witness exists. The adjacent excess law is `t = s − 1`; the
constrained law is additionally `s = a`. Every monomial-pair entry of the middle-band
probe tables is the cardinality of this explicit family. -/
theorem gap_badScalar_iff_excess (H : Finset F) {k s t a : ℕ}
    (hk : 1 ≤ k) (hkt : k ≤ t) (hts : t < s) (hka : k + 1 ≤ a) (has : a ≤ s) (lam : F) :
    (∃ q : Polynomial F, q.natDegree ≤ k - 1 ∧ a ≤ (gapAgreeSet H s t lam q).card) ↔
      GapWitness H k s t a lam := by
  constructor
  · rintro ⟨q, hq, hagree⟩
    exact gapWitness_of_badScalar hk hkt hts hka has hq hagree
  · intro hw
    exact badScalar_of_gapWitness hk hkt hts hka has hw

/-! ## Source audit -/

#print axioms gapWitness_of_badScalar
#print axioms badScalar_of_gapWitness
#print axioms gap_badScalar_iff_excess

end ArkLib.ProximityGap.GeneralGapCensus
