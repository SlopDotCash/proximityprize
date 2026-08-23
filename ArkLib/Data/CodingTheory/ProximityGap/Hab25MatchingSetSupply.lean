/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ShareGoodSetWeld
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CoordinateUpgradeWeld

/-!
# The matching-set supply (#304, leg 2 CLOSED)

The SK1 strict extraction consumes, per heavy cell, a family of heavy columns: more than
`deg w` columns `t`, each carrying more than `max(Bw, k)` scalars `z` at which the
decoded polynomial reads the fold section (`(P z).eval (domain t) = w_t(z)`).  This file
proves that supply from the decoded closeness alone, by double counting:

* `exists_many_heavy_columns` — the abstract brick: if every `z ∈ G` carries an
  agreement set of size `≥ c`, and the numeric regime `W·|G| + n·M < c·|G|` holds, then
  more than `W` columns each carry more than `M` scalars (count the incidence pairs two
  ways; if at most `W` columns were heavy the total would be `≤ W·|G| + n·M`);
* **`exists_matching_sets_of_decoded`** — the instantiation: for a decoded family on
  `G'` (closeness `δᵣ ≤ δ` at every scalar), with `c = n − ⌊δ·n⌋`, more than `W` columns
  each carry more than `M` scalars reading the fold section.  Taking `W := deg w` and
  `M := max Bw k` this is exactly the `Tset`/`Sset`/`hagree` input of
  `strict_coeffPolys_of_cell`, with the numeric regime
  `deg w·|G′| + n·max(Bw,k) < (n−⌊δn⌋)·|G′|` — the Johnson-regime arithmetic the
  keystone's parameters satisfy.

With this, leg 2 of the share-producer frontier is CLOSED; the single remaining open
input of the strict-Johnson lane is the per-heavy-cell surface supply (leg 1).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Finset
open _root_.ProximityGap Code
open scoped NNReal

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The heavy-columns double count.**  If every `z ∈ G` carries an agreement set of
size `≥ c` and `W·|G| + n·M < c·|G|`, then more than `W` columns each carry more than
`M` scalars: counting the incidence pairs two ways, at most `W` heavy columns would cap
the total at `W·|G| + n·M`. -/
theorem exists_many_heavy_columns {α : Type} [Fintype α] [DecidableEq α]
    {β : Type} [DecidableEq β]
    (G : Finset β) (S : β → Finset α) {c M W : ℕ}
    (hS : ∀ z ∈ G, c ≤ (S z).card)
    (hreg : W * G.card + Fintype.card α * M < c * G.card) :
    ∃ T : Finset α, W < T.card ∧
      ∀ t ∈ T, M < (G.filter (fun z => t ∈ S z)).card := by
  classical
  set T : Finset α :=
    Finset.univ.filter (fun t : α => M < (G.filter (fun z => t ∈ S z)).card) with hT
  refine ⟨T, ?_, fun t ht => (Finset.mem_filter.mp ht).2⟩
  by_contra h
  push Not at h
  -- the incidence count, column-wise
  have hdc : ∑ z ∈ G, (S z).card =
      ∑ t : α, (G.filter (fun z => t ∈ S z)).card := by
    calc ∑ z ∈ G, (S z).card
        = ∑ z ∈ G, ∑ t : α, if t ∈ S z then 1 else 0 := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]
      _ = ∑ t : α, ∑ z ∈ G, if t ∈ S z then 1 else 0 := Finset.sum_comm
      _ = ∑ t : α, (G.filter (fun z => t ∈ S z)).card := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.card_filter]
  -- the lower bound on the incidence count
  have hlow : c * G.card ≤ ∑ z ∈ G, (S z).card := by
    calc c * G.card = ∑ _z ∈ G, c := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ z ∈ G, (S z).card := Finset.sum_le_sum hS
  -- the upper bound when at most `W` columns are heavy
  have hup : ∑ t : α, (G.filter (fun z => t ∈ S z)).card ≤
      T.card * G.card + Fintype.card α * M := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t : α => M < (G.filter (fun z => t ∈ S z)).card)]
    have h1 : ∑ t ∈ T, (G.filter (fun z => t ∈ S z)).card ≤ T.card * G.card := by
      refine le_trans (Finset.sum_le_card_nsmul _ _ G.card
        (fun t _ => Finset.card_filter_le _ _)) ?_
      rw [smul_eq_mul]
    have h2 : ∑ t ∈ Finset.univ.filter
        (fun t : α => ¬ M < (G.filter (fun z => t ∈ S z)).card),
        (G.filter (fun z => t ∈ S z)).card ≤ Fintype.card α * M := by
      refine le_trans (Finset.sum_le_card_nsmul _ _ M
        (fun t ht => Nat.le_of_not_lt (Finset.mem_filter.mp ht).2)) ?_
      rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ (le_trans (Finset.card_filter_le _ _)
        (le_of_eq (Finset.card_univ)))
    exact Nat.add_le_add h1 h2
  have hWcap : T.card * G.card ≤ W * G.card := Nat.mul_le_mul_right _ h
  omega

/-- **The matching-set supply from decoded closeness (#304, leg 2).**  For a decoded
family on `G'` (relative closeness `δᵣ ≤ δ` at every scalar) in the numeric regime
`W·|G′| + n·M < (n − ⌊δ·n⌋)·|G′|`, more than `W` columns each carry more than `M`
scalars at which the decoded polynomial reads the fold section — exactly the
`Tset`/`Sset`/`hagree` input shape of `strict_coeffPolys_of_cell` at `W := deg w`,
`M := max Bw k`. -/
theorem exists_matching_sets_of_decoded {n L : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀)
    (u : WordStack F₀ (Fin L) (Fin n)) (δ : ℝ≥0)
    (G' : Finset F₀) (P : F₀ → F₀[X])
    (hP : ∀ γ ∈ G',
      δᵣ(∑ j : Fin L, (γ ^ (j : ℕ)) • u j, (P γ).eval ∘ domain) ≤ δ)
    {M W : ℕ}
    (hreg : W * G'.card + n * M <
      (n - Nat.floor (δ * n)) * G'.card) :
    ∃ T : Finset (Fin n), W < T.card ∧
      ∀ t ∈ T, M < (G'.filter (fun z =>
        (P z).eval (domain t) = (foldSectionAt u t).eval z)).card := by
  classical
  -- the per-scalar reading sets
  set S : F₀ → Finset (Fin n) := fun z =>
    Finset.univ.filter (fun t : Fin n =>
      (P z).eval (domain t) = (foldSectionAt u t).eval z) with hSdef
  -- each reading set is large: the closeness agreement set sits inside it
  have hS : ∀ z ∈ G', n - Nat.floor (δ * n) ≤ (S z).card := by
    intro z hz
    obtain ⟨S₀, hS₀card, hS₀agree⟩ :=
      (relCloseToWord_iff_exists_agreementCols
        (∑ j : Fin L, (z ^ (j : ℕ)) • u j) ((P z).eval ∘ domain) δ).mp (hP z hz)
    have hsub : S₀ ⊆ S z := by
      intro t ht
      have hread := (hS₀agree t).1 ht
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply] at hread
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [foldSectionAt_eval]
      exact hread.symm
    refine le_trans ?_ (Finset.card_le_card hsub)
    simpa [Fintype.card_fin] using hS₀card
  -- the double count
  obtain ⟨T, hTcard, hTheavy⟩ :=
    exists_many_heavy_columns (α := Fin n) (β := F₀) G' S hS
      (by simpa [Fintype.card_fin] using hreg)
  refine ⟨T, hTcard, fun t ht => ?_⟩
  have h := hTheavy t ht
  refine lt_of_lt_of_le h (le_of_eq (congrArg Finset.card ?_))
  refine Finset.filter_congr fun z _ => ?_
  simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_many_heavy_columns
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_matching_sets_of_decoded
