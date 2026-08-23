/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SbetaPackaging

/-!
# The exclusion count — Lemma A.1 in contrapositive counting form

The per-place data of the §5 heavy lane requires `π_z ξ ≠ 0` at every place used; the
places where a fixed nonzero `β` (in application: `ξ`) *does* vanish form `S_β β`, and
Lemma A.1 in contrapositive bounds any finite family of them by the weight budget:

  `embedding β ≠ 0 → ↑T ⊆ S_β β → weight ≤ W → T.card ≤ W·deg H`.

A cell larger than its useful-place threshold plus this exclusion budget therefore retains
a large sub-cell of places where `π_z ξ ≠ 0` — the cell-shrink step of the Claim 5.7
assembly, with the budget supplied by `ClaimA2.weight_ξ_bound` and the nonvanishing by
`embeddingOf𝒪Into𝕃_ξ_ne_zero`.

## References

* [BCIKS20] ePrint 2020/654, Appendix A.3 (Lemma A.1).
-/

open Polynomial Polynomial.Bivariate ToRatFunc Ideal BCIKS20AppendixA

namespace ArkLib

variable {F : Type} [Field F]

/-- **Lemma A.1, contrapositive counting form.**  A nonvanishing `β` admits at most
`W·deg H` matching points within any finite family, where `W` dominates its weight. -/
theorem finset_card_le_of_embedding_ne_zero {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hβ : embeddingOf𝒪Into𝕃 _ β ≠ 0)
    {W : ℕ} (hW : weight_Λ_over_𝒪 hH β D ≤ (W : WithBot ℕ))
    {T : Finset F} (hT : (↑T : Set F) ⊆ S_β β) :
    T.card ≤ W * H.natDegree := by
  by_contra hcon
  push_neg at hcon
  apply hβ
  refine embedding_eq_zero_of_finset_subset_S_β hH β D hD hT ?_
  have hmul : weight_Λ_over_𝒪 hH β D * (H.natDegree : WithBot ℕ)
      ≤ ((W * H.natDegree : ℕ) : WithBot ℕ) := by
    cases hwt : weight_Λ_over_𝒪 hH β D with
    | bot =>
        have hdH : ((H.natDegree : ℕ) : WithBot ℕ) ≠ 0 :=
          Nat.cast_ne_zero.mpr hH.ne'
        rw [WithBot.bot_mul hdH]
        exact bot_le
    | coe w =>
        have hwle : w ≤ W := by
          rw [hwt] at hW
          exact WithBot.coe_le_coe.mp hW
        simp only [Nat.cast_withBot]
        rw [← WithBot.coe_mul]
        exact WithBot.coe_le_coe.mpr (Nat.mul_le_mul_right H.natDegree hwle)
  refine lt_of_le_of_lt hmul ?_
  exact_mod_cast hcon

open Classical in
/-- **The cell-shrink.**  Removing the `β`-vanishing places from a cell costs at most
`W·deg H` elements: the surviving sub-cell of places with `π_z β ≠ 0` for every root
retains all but the exclusion budget. -/
theorem card_filter_pi_z_ne_zero_ge {H : F[X][Y]} [Fact (Irreducible H)] [DecidableEq F]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hβ : embeddingOf𝒪Into𝕃 _ β ≠ 0)
    {W : ℕ} (hW : weight_Λ_over_𝒪 hH β D ≤ (W : WithBot ℕ))
    (E : Finset F) :
    E.card - W * H.natDegree
      ≤ (E.filter (fun z => ∀ root : rationalRoot (H_tilde' H) z,
          (π_z z root) β ≠ 0)).card := by
  classical
  have hsplit : (E.filter (fun z => ∀ root : rationalRoot (H_tilde' H) z,
        (π_z z root) β ≠ 0)).card
      + (E.filter (fun z => ¬ ∀ root : rationalRoot (H_tilde' H) z,
          (π_z z root) β ≠ 0)).card = E.card :=
    Finset.card_filter_add_card_filter_not _
  have hbadsub : (↑(E.filter (fun z => ¬ ∀ root : rationalRoot (H_tilde' H) z,
      (π_z z root) β ≠ 0)) : Set F) ⊆ S_β β := by
    intro z hz
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hz
    obtain ⟨-, hz⟩ := hz
    push_neg at hz
    obtain ⟨root, hroot⟩ := hz
    exact ⟨root, hroot⟩
  have hbad := finset_card_le_of_embedding_ne_zero hH β D hD hβ hW hbadsub
  omega

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.finset_card_le_of_embedding_ne_zero
#print axioms ArkLib.card_filter_pi_z_ne_zero_ge
