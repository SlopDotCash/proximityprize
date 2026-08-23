/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Polynomial.RationalFunctions

/-!
# Packaging wrappers for `Lemma_A_1` (the `S_β` counting step of [BCIKS20] Appendix A)

The in-tree lemma `BCIKS20AppendixA.Lemma_A_1` concludes `embeddingOf𝒪Into𝕃 _ β = 0` from the
hypothesis that the set `S_β β` of "matching specialization points" is *strictly larger* than
`weight_Λ_over_𝒪 hH β D * H.natDegree` (the inequality lives in `WithBot ℕ`, with `Set.ncard`
coerced).

The eventual ingredient-C application produces a concrete *finite* set of matching points, i.e.
a `Finset F` `T` with `↑T ⊆ S_β β` and `#T` large.  This file discharges the bookkeeping that
turns such a `Finset` (or a numeric lower bound on `(S_β β).ncard`) into the hypothesis of
`Lemma_A_1`, so downstream work only has to exhibit `T`.

## Main results

* `ArkLib.S_β_finite_of_ne_zero` : `S_β β` is finite when `β ≠ 0`.
* `ArkLib.finset_card_le_ncard_S_β` : a `Finset` inside `S_β β` is bounded by the
  `ncard`, given `β ≠ 0`.
* `ArkLib.embedding_eq_zero_of_ncard_lower_bound` : `Lemma_A_1` fired from a numeric
  lower bound `N ≤ (S_β β).ncard` with `(N : WithBot ℕ) > Λ·d`.
* `ArkLib.embedding_eq_zero_of_finset_subset_S_β` : `Lemma_A_1` fired from a `Finset`
  `T ⊆ S_β β` with `(#T : WithBot ℕ) > Λ·d`.

-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal BCIKS20AppendixA

namespace ArkLib

variable {F : Type} [Field F]

/-- When `β` is a nonzero regular element, the set `S_β β` of matching specialization points is
finite: it is contained in the (finite) root set of the nonzero resultant
`Res_Y(canonicalRepOf𝒪 hH β, H_tilde' H)`. -/
lemma S_β_finite_of_ne_zero {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) {β : 𝒪 H} (hβ : β ≠ 0) :
    (S_β β).Finite := by
  classical
  set R := Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H) H.natDegree H.natDegree
    with hR_def
  have hR_ne : R ≠ 0 := resultant_canonicalRep_H_tilde'_ne_zero hH hβ
  have hsubset : S_β β ⊆ {z : F | R.IsRoot z} := by
    intro z hz
    have := eval_resultant_eq_zero_of_mem_S_β hH β hz
    rw [← hR_def] at this
    exact this
  exact (Polynomial.finite_setOf_isRoot hR_ne).subset hsubset

/-- A `Finset` of matching points sitting inside `S_β β` has cardinality bounded by the `ncard` of
`S_β β`, provided `β ≠ 0` (which guarantees `S_β β` is finite). -/
lemma finset_card_le_ncard_S_β {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) {β : 𝒪 H} (hβ : β ≠ 0) {T : Finset F}
    (hT : (↑T : Set F) ⊆ S_β β) :
    T.card ≤ (S_β β).ncard := by
  classical
  have hfin : (S_β β).Finite := S_β_finite_of_ne_zero hH hβ
  have := Set.ncard_le_ncard hT hfin
  rwa [Set.ncard_coe_finset] at this

/-- **Packaging form of `Lemma_A_1` from a numeric `ncard` lower bound.**

If `S_β β` has at least `N` matching points (`N ≤ (S_β β).ncard`) and `N` already beats the bound
`weight_Λ_over_𝒪 hH β D * H.natDegree` (inequality in `WithBot ℕ`), then the embedding of `β`
into the function field `𝕃` is zero. -/
lemma embedding_eq_zero_of_ncard_lower_bound {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {N : ℕ} (hN : N ≤ (S_β β).ncard)
    (hbig : (↑N : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree) :
    embeddingOf𝒪Into𝕃 _ β = 0 := by
  -- Promote the lower bound to the exact hypothesis required by `Lemma_A_1`.
  have hmono : (↑N : WithBot ℕ) ≤ (↑(Set.ncard (S_β β)) : WithBot ℕ) := by
    exact_mod_cast hN
  have hcard : Set.ncard (S_β β) > weight_Λ_over_𝒪 hH β D * H.natDegree := lt_of_lt_of_le hbig hmono
  exact Lemma_A_1 hH β D hD hcard

/-- **Packaging form of `Lemma_A_1` from a `Finset` of matching points.**

The eventual ingredient-C application only needs to exhibit a `Finset F` `T` with `↑T ⊆ S_β β`
whose cardinality exceeds the weight bound `weight_Λ_over_𝒪 hH β D * H.natDegree` (in `WithBot ℕ`).
This brick discharges everything else, concluding `embeddingOf𝒪Into𝕃 _ β = 0`
(which feeds `alpha'_eq_zero_of_embedding_beta_eq_zero` → Claim 5.8). -/
lemma embedding_eq_zero_of_finset_subset_S_β {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {T : Finset F} (hT : (↑T : Set F) ⊆ S_β β)
    (hcard : (↑T.card : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree) :
    embeddingOf𝒪Into𝕃 _ β = 0 := by
  classical
  -- If `β = 0` the conclusion is immediate; otherwise `S_β β` is finite and we count.
  by_cases hβ : β = 0
  · subst hβ; simp
  · refine embedding_eq_zero_of_ncard_lower_bound hH β D hD
      (N := T.card) (finset_card_le_ncard_S_β hH hβ hT) hcard

end ArkLib

#print axioms ArkLib.S_β_finite_of_ne_zero
#print axioms ArkLib.finset_card_le_ncard_S_β
#print axioms ArkLib.embedding_eq_zero_of_ncard_lower_bound
#print axioms ArkLib.embedding_eq_zero_of_finset_subset_S_β
