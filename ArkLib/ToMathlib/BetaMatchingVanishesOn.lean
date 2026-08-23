/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaMatchingVanishes

/-!
#304 brick: restricted-root (membership-dependent) consumer chain for ingredient C.

Satisfiability finding #3 on issue #304: every §5 bundle carries a TOTAL family
`root : (z : F) → rationalRoot (H_tilde' H) z`, which is unsatisfiable for typical GS
factors (the fibre type is empty at non-split `z`). Every USE of `root` is at matching-set
members only, so the honest shape is `rootOn : ∀ z ∈ matchingSet, rationalRoot …`.

This file transports the ingredient-C consumer chain to the restricted form:
* `MatchingVanishesOn` — the restricted-root isolated property `P β`;
* `matchingVanishesOn_of_matchingVanishes` — total ⟹ restricted (wiring old suppliers);
* `matchingSet_subset_S_β_of_POn` — restricted L14 bridge;
* `embedding_eq_zero_of_matchingSet_largeOn` — restricted ingredient-C deliverable;
* `exists_rootOn_matchingVanishesOn_iff_subset_S_β` — the restricted family exists IFF
  `↑matchingSet ⊆ S_β β` (so the restricted form is the faithful one);
* `not_exists_total_matchingVanishes_of_isEmpty` /
  `exists_rootOn_not_exists_root_of_isEmpty` — formalized finding #3: one empty fibre
  (a non-split point of `H`) kills every total family, while the restricted family still
  exists whenever `↑matchingSet ⊆ S_β β`;
* `betaRec_matchingVanishesOn`, `betaRec_embedding_eq_zero_of_matchingSet_largeOn` —
  the `betaRec` keystone chain (Claim 5.8 hypothesis) in restricted-root form.
-/


set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace IngredientC

variable {F : Type} [Field F]

/-- **Restricted-root isolated property `P(β)`.**  The membership-dependent form of
`MatchingVanishes`: the rational-root section is only demanded at matching-set members,
so the datum is satisfiable for GS factors that are not fibrewise totally split. -/
def MatchingVanishesOn {H : F[X][Y]} (matchingSet : Finset F)
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z) (β : 𝒪 H) : Prop :=
  ∀ z (hz : z ∈ matchingSet), (π_z z (rootOn z hz)) β = 0

/-- A total-family `MatchingVanishes` restricts to `MatchingVanishesOn` (wiring lemma for
existing total-root suppliers). -/
lemma matchingVanishesOn_of_matchingVanishes {H : F[X][Y]} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z} {β : 𝒪 H}
    (hP : MatchingVanishes matchingSet root β) :
    MatchingVanishesOn matchingSet (fun z _ => root z) β :=
  fun z hz => hP z hz

/-- **Restricted converse bridge (L14).**  `MatchingVanishesOn` puts the matching set inside
`S_β β` — verbatim transport of `matchingSet_subset_S_β_of_P`. -/
lemma matchingSet_subset_S_β_of_POn {H : F[X][Y]} {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z} {β : 𝒪 H}
    (hP : MatchingVanishesOn matchingSet rootOn β) :
    (↑matchingSet : Set F) ⊆ S_β β := by
  intro z hz
  have hz' : z ∈ matchingSet := by simpa using hz
  exact mem_S_β_of_pi_z_eq_zero β (rootOn z hz') (hP z hz')

/-- **Restricted ingredient-C deliverable.**  `MatchingVanishesOn` + the `Λ·d` largeness give
`embedding β = 0`. -/
theorem embedding_eq_zero_of_matchingSet_largeOn {H : F[X][Y]} [Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {matchingSet : Finset F} {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (hP : MatchingVanishesOn matchingSet rootOn β)
    (hcard : (↑matchingSet.card : WithBot ℕ) > weight_Λ_over_𝒪 hH β D * H.natDegree) :
    embeddingOf𝒪Into𝕃 _ β = 0 :=
  embedding_eq_zero_of_finset_subset_S_β hH β D hD (matchingSet_subset_S_β_of_POn hP) hcard

/-- **Faithfulness of the restricted form.**  A restricted-root family with the vanishing
property exists IFF the matching set sits inside `S_β β`.  (The total form only gives the
forward direction in general: the reverse demands rational roots at every `z : F`.) -/
theorem exists_rootOn_matchingVanishesOn_iff_subset_S_β {H : F[X][Y]}
    {matchingSet : Finset F} {β : 𝒪 H} :
    (∃ rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z,
        MatchingVanishesOn matchingSet rootOn β) ↔
      (↑matchingSet : Set F) ⊆ S_β β := by
  constructor
  · rintro ⟨rootOn, hP⟩
    exact matchingSet_subset_S_β_of_POn hP
  · intro hsub
    have h : ∀ z (_ : z ∈ matchingSet),
        ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0 :=
      fun z hz => hsub (Finset.mem_coe.mpr hz)
    choose rootOn hrootOn using h
    exact ⟨rootOn, hrootOn⟩

/-- **Finding #3, formalized (negative half).**  One empty rational-root fibre — a single
non-split point `z₀` of `H`, which exists for every GS factor that is not fibrewise totally
split — makes EVERY total-root family `root : (z : F) → rationalRoot (H_tilde' H) z`
non-existent, hence every total-form `MatchingVanishes` datum unsatisfiable, regardless of
`matchingSet` and `β`. -/
lemma not_exists_total_matchingVanishes_of_isEmpty {H : F[X][Y]} {matchingSet : Finset F}
    {β : 𝒪 H} (z₀ : F) (h : IsEmpty (rationalRoot (H_tilde' H) z₀)) :
    ¬ ∃ root : (z : F) → rationalRoot (H_tilde' H) z,
        MatchingVanishes matchingSet root β :=
  fun ⟨root, _⟩ => h.elim (root z₀)

/-- **Finding #3, formalized (strictness).**  If some fibre is empty but the matching set sits
inside `S_β β`, then the restricted-root datum exists while the total-root datum does not:
the restricted form is *strictly* more general, and is the honest shape for the §5 bundles. -/
theorem exists_rootOn_not_exists_root_of_isEmpty {H : F[X][Y]} {matchingSet : Finset F}
    {β : 𝒪 H} (z₀ : F) (h : IsEmpty (rationalRoot (H_tilde' H) z₀))
    (hsub : (↑matchingSet : Set F) ⊆ S_β β) :
    (∃ rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z,
        MatchingVanishesOn matchingSet rootOn β) ∧
      ¬ ∃ root : (z : F) → rationalRoot (H_tilde' H) z,
          MatchingVanishes matchingSet root β :=
  ⟨exists_rootOn_matchingVanishesOn_iff_subset_S_β.mpr hsub,
    not_exists_total_matchingVanishes_of_isEmpty z₀ h⟩

end IngredientC

namespace BetaMatchingVanishes

variable {F : Type} [Field F]

/-- **Restricted-root L12 → L14 keystone.**  Per-point matching data at matching-set members
only (no off-set rational roots demanded) yield `MatchingVanishesOn` for `betaRec … t`. -/
theorem betaRec_matchingVanishesOn (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ)
    {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (mp : ∀ z (hz : z ∈ matchingSet),
      MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz)) :
    ArkLib.IngredientC.MatchingVanishesOn matchingSet rootOn
      (betaRec x₀ R H hHyp Bcoeff t) :=
  fun z hz => (mp z hz).pi_z_eq_zero

/-- **Restricted-root Claim-5.8 hypothesis for `betaRec`.**  Per-point matching data at
matching-set members + the L9 weight bound give `embedding (betaRec … t) = 0`. -/
theorem betaRec_embedding_eq_zero_of_matchingSet_largeOn (x₀ : F) (R : F[X][X][Y])
    (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (mp : ∀ z (hz : z ∈ matchingSet),
      MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz))
    (hcard : (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree) :
    embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  ArkLib.IngredientC.embedding_eq_zero_of_matchingSet_largeOn hH
    (betaRec x₀ R H hHyp Bcoeff t) D hD
    (betaRec_matchingVanishesOn x₀ R H hHyp Bcoeff t mp) hcard

end BetaMatchingVanishes

end ArkLib

#print axioms ArkLib.IngredientC.matchingVanishesOn_of_matchingVanishes
#print axioms ArkLib.IngredientC.matchingSet_subset_S_β_of_POn
#print axioms ArkLib.IngredientC.embedding_eq_zero_of_matchingSet_largeOn
#print axioms ArkLib.IngredientC.exists_rootOn_matchingVanishesOn_iff_subset_S_β
#print axioms ArkLib.IngredientC.not_exists_total_matchingVanishes_of_isEmpty
#print axioms ArkLib.IngredientC.exists_rootOn_not_exists_root_of_isEmpty
#print axioms ArkLib.BetaMatchingVanishes.betaRec_matchingVanishesOn
#print axioms ArkLib.BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_largeOn
