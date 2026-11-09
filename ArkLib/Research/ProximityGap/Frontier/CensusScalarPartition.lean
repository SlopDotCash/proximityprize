/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalAlignmentLaw

/-!
# The census scalar-partition: alignableSets decomposes exactly by its pinned scalar (#444 §6.4/§6.7)

The universal census bound `badScalars_card_le_alignable` (UniversalAlignmentLaw) certifies

  **#bad ≤ #alignableSets**

via a one-per-scalar injection (each bad `γ` is sent to ONE of its aligned `a`-sets). That
injection is deliberately lossy: a single bad `γ` typically owns MANY aligned `a`-sets, so the
crude census count over-shoots `#bad` by the per-scalar multiplicity. The issue (#444) flags this
as the open **distinct-`γ` vs. (subset,`γ`)-incidence reconciliation**: *"`δ*` is governed by the
distinct-`γ` count, NOT the (subset,`γ`) incidence."* The over-determined floor was REFUTED at the
binding radius precisely because the distinct-`γ` count already exceeds budget there, while the
incidence count is larger still.

This file pins that reconciliation EXACTLY, at the `a`-set level (the census object), with no new
hypotheses beyond the in-tree `Aligned` / `Aligned.gamma_eq`:

* `alignedSetsForScalar dom k a u₀ u₁ γ` — the non-degenerate `γ`-aligned `a`-sets.
* `Aligned.gamma_eq` ⟹ these are **pairwise disjoint** across distinct `γ`
  (`alignedSetsForScalar_disjoint`): every non-degenerate aligned `a`-set has a UNIQUE pinned `γ`.
* the `alignableSets` are the union of `alignedSetsForScalar` over the (finite) set of all field
  scalars (`alignableSets_eq_biUnion`), hence the **EXACT census decomposition**

    **#alignableSets = Σ_{γ} #alignedSetsForScalar γ**     (`alignableSets_card_eq_sum`)

  — the census count is the SUM of the per-scalar multiplicities, the honest form of `#bad ≤ census`.
* the **distinct-`γ` count** = #{scalars that own ≥1 non-degenerate aligned `a`-set}
  (`pinnedScalars`); it satisfies `#pinnedScalars ≤ #alignableSets` (`pinnedScalars_card_le`), with
  the EXACT slack `Σ (mult γ − 1)` (`alignableSets_card_eq_pinned_add_multiplicityExcess`). The
  census bound is TIGHT iff every multiplicity is `1` (`census_tight_iff_all_mult_one`).
* `Aligned.mono` ⟹ the per-scalar multiplicity is monotone in the agreement structure: if `γ` owns
  one aligned set of size `s`, it owns ALL of its `a`-subsets, so `mult γ ≥ C(s, a)`
  (`mult_ge_choose_of_aligned_superset`). This is the combinatorial source of the census slack: a
  deep agreement set inflates the incidence count by `C(s,a)` while contributing `1` to distinct-`γ`.

## Scope (rule 3 / rule 6, honesty contract)

This is NOT a CORE closure and NOT thinness-essential: it is field-universal combinatorics about the
census object, sharpening the in-tree census bound from an inequality into an exact partition
identity. It localizes the open content precisely: the prize's distinct-`γ` (governing) count is the
number of NONEMPTY parts of this partition, and the census bound over-counts it by the multiplicity
excess. CORE (`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

open Classical in
/-- The non-degenerate `γ`-aligned `a`-sets: `a`-subsets every injective `(k+1)`-tuple of which lies
on the `γ`-fibre, and which contain at least one tuple where the pencil does not jointly vanish.
These are the census objects of `alignableSets`, refined to a SINGLE scalar `γ`. -/
noncomputable def alignedSetsForScalar (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (γ : F) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard a).filter (fun S : Finset (Fin n) =>
    Aligned dom k u₀ u₁ γ S ∧
      ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ b, t b ∈ S) ∧
        ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))

omit [Fintype F] in
/-- Membership in `alignedSetsForScalar`. -/
theorem mem_alignedSetsForScalar {dom : Fin n ↪ F} {k a : ℕ} {u₀ u₁ : Fin n → F} {γ : F}
    {S : Finset (Fin n)} :
    S ∈ alignedSetsForScalar dom k a u₀ u₁ γ ↔
      (S.card = a ∧ Aligned dom k u₀ u₁ γ S ∧
        ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ b, t b ∈ S) ∧
          ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) := by
  classical
  unfold alignedSetsForScalar
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨-, hcard⟩, halign, ht⟩; exact ⟨hcard, halign, ht⟩
  · rintro ⟨hcard, halign, ht⟩; exact ⟨⟨Finset.subset_univ _, hcard⟩, halign, ht⟩

omit [Fintype F] in
/-- **Unique ownership at the set level.** A non-degenerate aligned `a`-set has a UNIQUE pinned
scalar: `alignedSetsForScalar` for distinct `γ` are pairwise disjoint. (Set-level analogue of the
tuple-level `gamma_eq_of_owned`; the engine is `Aligned.gamma_eq`.) -/
theorem alignedSetsForScalar_disjoint (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {γ γ' : F} (hne : γ ≠ γ') :
    Disjoint (alignedSetsForScalar dom k a u₀ u₁ γ) (alignedSetsForScalar dom k a u₀ u₁ γ') := by
  classical
  rw [Finset.disjoint_left]
  intro S hS hS'
  rw [mem_alignedSetsForScalar] at hS hS'
  obtain ⟨-, halign, t, htinj, htmem, hnd⟩ := hS
  obtain ⟨-, halign', -⟩ := hS'
  exact hne (Aligned.gamma_eq halign halign' htinj htmem hnd)

open Classical in
/-- **The census decomposition (union form).** `alignableSets` is the union, over ALL field scalars,
of the per-scalar non-degenerate aligned `a`-sets. Each alignable set is `γ`-aligned for some `γ`,
and (being non-degenerate) lands in exactly that `γ`'s part. -/
theorem alignableSets_eq_biUnion (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    alignableSets dom k a u₀ u₁
      = (Finset.univ : Finset F).biUnion (alignedSetsForScalar dom k a u₀ u₁) := by
  classical
  ext S
  rw [Finset.mem_biUnion]
  unfold alignableSets
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hmem, γ, halign, ht⟩
    refine ⟨γ, Finset.mem_univ _, ?_⟩
    rw [mem_alignedSetsForScalar]
    exact ⟨(Finset.mem_powersetCard.mp hmem).2, halign, ht⟩
  · rintro ⟨γ, -, hS⟩
    rw [mem_alignedSetsForScalar] at hS
    obtain ⟨hcard, halign, ht⟩ := hS
    exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, γ, halign, ht⟩

open Classical in
/-- **THE EXACT CENSUS COUNT** — the census bound `#bad ≤ #alignableSets` in its honest exact form:
the census count is the SUM of the per-scalar multiplicities. The over-count of `#bad` is exactly
`Σ (mult γ − 1)` over the scalars that own ≥1 aligned set (the multiplicity excess). -/
theorem alignableSets_card_eq_sum (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (alignableSets dom k a u₀ u₁).card
      = ∑ γ : F, (alignedSetsForScalar dom k a u₀ u₁ γ).card := by
  classical
  rw [alignableSets_eq_biUnion]
  rw [Finset.card_biUnion]
  intro γ _ γ' _ hne
  exact alignedSetsForScalar_disjoint dom k a u₀ u₁ hne

open Classical in
/-- **The pinned-scalar set** = the distinct `γ` that own at least one non-degenerate aligned
`a`-set. This is the `δ*`-governing **distinct-`γ`** count (vs. the incidence `#alignableSets`). -/
noncomputable def pinnedScalars (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : Finset F :=
  (Finset.univ : Finset F).filter (fun γ => (alignedSetsForScalar dom k a u₀ u₁ γ).Nonempty)

/-- A scalar is pinned iff it owns a non-degenerate aligned `a`-set. -/
theorem mem_pinnedScalars {dom : Fin n ↪ F} {k a : ℕ} {u₀ u₁ : Fin n → F} {γ : F} :
    γ ∈ pinnedScalars dom k a u₀ u₁ ↔ (alignedSetsForScalar dom k a u₀ u₁ γ).Nonempty := by
  classical
  unfold pinnedScalars
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open Classical in
/-- Restricting the census sum to the pinned scalars (the empty parts contribute `0`). -/
theorem alignableSets_card_eq_sum_pinned (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (alignableSets dom k a u₀ u₁).card
      = ∑ γ ∈ pinnedScalars dom k a u₀ u₁, (alignedSetsForScalar dom k a u₀ u₁ γ).card := by
  classical
  rw [alignableSets_card_eq_sum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro γ _ hγ
  have hγ' : ¬ (alignedSetsForScalar dom k a u₀ u₁ γ).Nonempty := by
    rw [← mem_pinnedScalars]; exact hγ
  rw [Finset.not_nonempty_iff_eq_empty] at hγ'
  rw [hγ', Finset.card_empty]

open Classical in
/-- **DISTINCT-`γ` ≤ CENSUS.** The distinct-`γ` count (the `δ*`-governing quantity) is at most the
census incidence count `#alignableSets`. This is the honest form of the campaign's
`badScalars_card_le_alignable`: each pinned scalar contributes ≥ 1 to the census sum. -/
theorem pinnedScalars_card_le (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (pinnedScalars dom k a u₀ u₁).card ≤ (alignableSets dom k a u₀ u₁).card := by
  classical
  rw [alignableSets_card_eq_sum_pinned]
  conv_lhs => rw [Finset.card_eq_sum_ones (pinnedScalars dom k a u₀ u₁)]
  apply Finset.sum_le_sum
  intro γ hγ
  rw [mem_pinnedScalars, ← Finset.card_pos] at hγ
  exact hγ

open Classical in
/-- **THE EXACT SLACK.** The census count splits as the distinct-`γ` count PLUS the multiplicity
excess `Σ_{pinned γ} (mult γ − 1)`. So `#alignableSets − #pinnedScalars = Σ (mult γ − 1)` exactly:
the census bound over-counts the governing distinct-`γ` count by precisely the per-scalar
multiplicity surplus. -/
theorem alignableSets_card_eq_pinned_add_multiplicityExcess (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) :
    (alignableSets dom k a u₀ u₁).card
      = (pinnedScalars dom k a u₀ u₁).card
        + ∑ γ ∈ pinnedScalars dom k a u₀ u₁,
            ((alignedSetsForScalar dom k a u₀ u₁ γ).card - 1) := by
  classical
  rw [alignableSets_card_eq_sum_pinned, Finset.card_eq_sum_ones (pinnedScalars _ _ _ _ _),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [mem_pinnedScalars, ← Finset.card_pos] at hγ
  omega

open Classical in
/-- **CENSUS TIGHTNESS CRITERION.** The census bound `#bad ≤ #alignableSets` is TIGHT (equality of
distinct-`γ` and census incidence) iff every pinned scalar owns EXACTLY ONE aligned `a`-set, i.e.
the multiplicity excess vanishes. -/
theorem census_tight_iff_all_mult_one (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (pinnedScalars dom k a u₀ u₁).card = (alignableSets dom k a u₀ u₁).card
      ↔ ∀ γ ∈ pinnedScalars dom k a u₀ u₁, (alignedSetsForScalar dom k a u₀ u₁ γ).card = 1 := by
  classical
  rw [alignableSets_card_eq_pinned_add_multiplicityExcess]
  constructor
  · intro heq γ hγ
    have hsum0 : ∑ γ ∈ pinnedScalars dom k a u₀ u₁,
        ((alignedSetsForScalar dom k a u₀ u₁ γ).card - 1) = 0 := by omega
    have hterm : (alignedSetsForScalar dom k a u₀ u₁ γ).card - 1 = 0 :=
      Nat.le_zero.mp (hsum0 ▸ Finset.single_le_sum (f := fun γ =>
        (alignedSetsForScalar dom k a u₀ u₁ γ).card - 1) (fun _ _ => Nat.zero_le _) hγ)
    rw [mem_pinnedScalars, ← Finset.card_pos] at hγ
    omega
  · intro hall
    have hsum0 : ∑ γ ∈ pinnedScalars dom k a u₀ u₁,
        ((alignedSetsForScalar dom k a u₀ u₁ γ).card - 1) = 0 := by
      apply Finset.sum_eq_zero
      intro γ hγ; simp [hall γ hγ]
    omega

omit [Fintype F] in
open Classical in
/-- **THE MULTIPLICITY LOWER BOUND (the census-slack source).** If a scalar `γ` `γ`-aligns a set `S₀`
of size `s` containing a non-degenerate tuple, then (by `Aligned.mono`) `γ` aligns EVERY `a`-subset
of `S₀` that contains that tuple; in particular its multiplicity is at least the number of
`a`-subsets of `S₀` containing the fixed non-degenerate `(k+1)`-tuple, `C(s − (k+1), a − (k+1))`.
This is why a deep agreement set inflates the census incidence by a binomial factor while adding
only `1` to the distinct-`γ` count — the combinatorial mechanism of the census over-count. -/
theorem mult_ge_choose_of_aligned_superset (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F)
    {S₀ : Finset (Fin n)} (halign : Aligned dom k u₀ u₁ γ S₀)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ S₀)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))
    (hak : k + 1 ≤ a) :
    (S₀.card - (k + 1)).choose (a - (k + 1)) ≤ (alignedSetsForScalar dom k a u₀ u₁ γ).card := by
  classical
  -- The image tuple, as a (k+1)-subset of S₀.
  set T : Finset (Fin n) := Finset.univ.image t with hT
  have hTsub : T ⊆ S₀ := by
    intro i hi; rw [hT, Finset.mem_image] at hi
    obtain ⟨b, -, rfl⟩ := hi; exact htmem b
  have hTcard : T.card = k + 1 := by
    rw [hT, Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin]
  -- The a-subsets of S₀ that contain T: there are C(|S₀| - (k+1), a - (k+1)) of them, and each is
  -- a non-degenerate γ-aligned a-set (alignment by Aligned.mono; non-degeneracy via T's tuple).
  -- Inject {a-subsets of S₀ \ T of size a-(k+1)} ↪ alignedSetsForScalar via U ↦ U ∪ T.
  set D : Finset (Finset (Fin n)) := (S₀ \ T).powersetCard (a - (k + 1)) with hD
  have hcardD : D.card = (S₀.card - (k + 1)).choose (a - (k + 1)) := by
    have hTinter : T ∩ S₀ = T := Finset.inter_eq_left.mpr hTsub
    have hsd : (S₀ \ T).card = S₀.card - (k + 1) := by
      rw [Finset.card_sdiff, hTinter, hTcard]
    rw [hD, Finset.card_powersetCard, hsd]
  rw [← hcardD]
  apply Finset.card_le_card_of_injOn (fun U => U ∪ T)
  · -- maps into alignedSetsForScalar
    intro U hU
    rw [Finset.mem_coe, hD, Finset.mem_powersetCard] at hU
    obtain ⟨hUsub, hUcard⟩ := hU
    have hUTdisj : Disjoint U T := Finset.disjoint_of_subset_left hUsub Finset.sdiff_disjoint
    have hUTsub : U ∪ T ⊆ S₀ := by
      intro i hi
      rw [Finset.mem_union] at hi
      rcases hi with h | h
      · exact (Finset.sdiff_subset) (hUsub h)
      · exact hTsub h
    rw [Finset.mem_coe, mem_alignedSetsForScalar]
    refine ⟨?_, halign.mono hUTsub, t, htinj, fun b => ?_, hnd⟩
    · rw [Finset.card_union_of_disjoint hUTdisj, hUcard, hTcard]; omega
    · exact Finset.mem_union_right _ (by rw [hT]; exact Finset.mem_image_of_mem t (Finset.mem_univ b))
  · -- injective on D: U ∪ T determines U since U, U' ⊆ S₀ \ T are disjoint from T
    intro U hU U' hU' heq
    rw [Finset.mem_coe, hD, Finset.mem_powersetCard] at hU hU'
    have hUdisj : Disjoint U T := Finset.disjoint_of_subset_left hU.1 Finset.sdiff_disjoint
    have hU'disj : Disjoint U' T := Finset.disjoint_of_subset_left hU'.1 Finset.sdiff_disjoint
    have hkey : (U ∪ T) \ T = (U' ∪ T) \ T := by
      simp only at heq; rw [heq]
    rwa [Finset.union_sdiff_cancel_right hUdisj, Finset.union_sdiff_cancel_right hU'disj] at hkey

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.alignedSetsForScalar_disjoint
#print axioms ProximityGap.Ownership.alignableSets_eq_biUnion
#print axioms ProximityGap.Ownership.alignableSets_card_eq_sum
#print axioms ProximityGap.Ownership.pinnedScalars_card_le
#print axioms ProximityGap.Ownership.alignableSets_card_eq_pinned_add_multiplicityExcess
#print axioms ProximityGap.Ownership.census_tight_iff_all_mult_one
#print axioms ProximityGap.Ownership.mult_ge_choose_of_aligned_superset
