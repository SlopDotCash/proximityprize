/-
# Fintype-free antipodal transversal for negation-closed sets (#444, de-Fintype rung)

The strata count `negSymCount G 6 = 15|G|³ − 45|G|² + 40|G|`
(`E3Assembly.negSymCount_eq_closed`) and its consumers are proven only under `[Fintype F]`, because
the in-tree `E3StrataCount.exists_neg_transversal` builds the one-representative-per-antipodal-pair
transversal `T = G.filter (· ≤ −·)` using a `LinearOrder F` obtained from `Fintype.equivFin F`. That
`[Fintype F]` is the sole obstruction to applying the closed form over a characteristic-0 field
(`μ_n ⊂ ℂ`), which is the precisely-mapped wall in DISPROOF_LOG
`[doorIV-e3-char0-closedform-fintype-barrier]`.

This file removes the `[Fintype F]` from the transversal existence statement. The key observation is
that the transversal construction needs only SOME linear order on `F`, not a field- or
finite-derived one, and `Classical` well-ordering (`WellOrderingRel`) supplies a `LinearOrder F` for
ANY type `F` with no `Fintype`. The resulting `exists_neg_transversal_of_no_fintype` is identical in
conclusion to the in-tree `[Fintype F]` version but holds over any `[Field F] [DecidableEq F]` — it
is the first concrete rung toward a `Fintype`-free (char-0-applicable) `negSymCount` closed form.

## Scope / honesty
This proves ONLY the transversal existence (`|G|` even, one rep per antipodal pair), `Fintype`-free.
It does NOT yet prove the `negSymCount` closed form `Fintype`-free (the strata-count proof has other
`[Fintype F]` uses to audit/remove), and makes NO
CORE/cancellation/completion/moment-saving/capacity claim. It is a structural de-`Fintype` enabling
lemma.
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Basic

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.AntipodalTransversalFintypeFree

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- A negation-closed finite set `G` with `0 ∉ G` over a field of characteristic `≠ 2` has a
**representative transversal** for the antipodal pairing `x ↦ −x`: a subset `T ⊆ G` that, together
with its negation `T.image (−·)`, partitions `G` into disjoint halves, so `2·|T| = |G|`.

Unlike `E3StrataCount.exists_neg_transversal`, this version carries **no `[Fintype F]`**: the only
ingredient that needed it was a linear order on `F` to choose the smaller element of each pair, and
`Classical` well-ordering (`WellOrderingRel`) supplies one for any type. -/
theorem exists_neg_transversal_of_no_fintype (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    ∃ T : Finset F, T ⊆ G ∧ Disjoint T (T.image (fun x => -x))
      ∧ T ∪ T.image (fun x => -x) = G ∧ 2 * T.card = G.card := by
  classical
  -- A linear order on `F` from Classical well-ordering — NO `Fintype` needed.
  letI : LinearOrder F := IsWellOrder.linearOrder (WellOrderingRel (α := F))
  have hxne : ∀ x ∈ G, x ≠ -x := by
    intro x hx hcontra
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    have h2a : (2 : F) * x = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2a with h' | h'
    · exact h2 h'
    · exact hx0 h'
  set T := G.filter (fun x => x ≤ -x) with hTdef
  have hsub : T ⊆ G := Finset.filter_subset _ _
  have hdisj : Disjoint T (T.image (fun x => -x)) := by
    rw [Finset.disjoint_left]
    intro a haT haI
    rw [hTdef, Finset.mem_filter] at haT
    rw [Finset.mem_image] at haI
    obtain ⟨b, hbT, hba⟩ := haI
    rw [hTdef, Finset.mem_filter] at hbT
    have hab : a = -b := hba.symm
    have hbne : b ≠ -b := hxne b hbT.1
    have hle2 : -b ≤ b := by rw [hab] at haT; simpa using haT.2
    exact hbne (le_antisymm hbT.2 hle2)
  have hcov : T ∪ T.image (fun x => -x) = G := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hsub h
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
        exact hneg y (hsub hy)
    · intro x hx
      rw [Finset.mem_union]
      by_cases hle : x ≤ -x
      · exact Or.inl (by rw [hTdef, Finset.mem_filter]; exact ⟨hx, hle⟩)
      · right
        rw [Finset.mem_image]
        exact ⟨-x, by rw [hTdef, Finset.mem_filter]
                      exact ⟨hneg x hx, by simp only [neg_neg]; exact (not_le.mp hle).le⟩,
               by simp⟩
  refine ⟨T, hsub, hdisj, hcov, ?_⟩
  have himg : (T.image (fun x => -x)).card = T.card :=
    Finset.card_image_of_injective _ neg_injective
  have hu := Finset.card_union_of_disjoint hdisj
  rw [hcov, himg] at hu
  omega


/-- **Fintype-free negation-closed subset count.**  If `G` is closed under negation, avoids zero,
and the field has characteristic not two, then the number of negation-closed `2i`-subsets of `G`
is `choose(|G|/2,i)`, without any ambient `[Fintype F]` assumption.  This ports
`E3SubsetCount.negClosed_subset_count` through `exists_neg_transversal_of_no_fintype`. -/
theorem negClosed_subset_count_of_no_fintype (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) (i : ℕ) :
    (G.powerset.filter (fun S => (∀ z ∈ S, -z ∈ S) ∧ S.card = 2 * i)).card
      = Nat.choose (G.card / 2) i := by
  classical
  obtain ⟨T, hsubT, hdisj, hcov, hTcard⟩ := exists_neg_transversal_of_no_fintype G h2 h0 hneg
  have hTc : T.card = G.card / 2 := by omega
  rw [← hTc, ← Finset.card_powersetCard i T]
  refine Finset.card_nbij' (fun S => S ∩ T) (fun U => U ∪ U.image (fun x => -x)) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSG, hClosed, hcard⟩ := hS
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.inter_subset_right, ?_⟩
    show (S ∩ T).card = i
    have hsplit : S = (S ∩ T) ∪ (S ∩ T).image (fun x => -x) := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hmem : x ∈ T ∪ T.image (fun x => -x) := hcov ▸ hSG hx
        rw [Finset.mem_union] at hmem
        rcases hmem with hT | hiT
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hT⟩)
        · rw [Finset.mem_image] at hiT; obtain ⟨y, hy, rfl⟩ := hiT
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, ?_, rfl⟩)
          exact Finset.mem_inter.mpr ⟨by have := hClosed (-y) hx; rwa [neg_neg] at this, hy⟩
      · intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with h | h
        · exact (Finset.mem_inter.mp h).1
        · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
          exact hClosed y (Finset.mem_inter.mp hy).1
    have hdisj' : Disjoint (S ∩ T) ((S ∩ T).image (fun x => -x)) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right (Finset.image_subset_image Finset.inter_subset_right) hdisj)
    have hc : S.card = 2 * (S ∩ T).card := by
      conv_lhs => rw [hsplit]
      rw [Finset.card_union_of_disjoint hdisj', Finset.card_image_of_injective _ neg_injective]; ring
    omega
  · intro U hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUT, hUcard⟩ := hU
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    have hUG : U ⊆ G := hUT.trans hsubT
    have hd : Disjoint U (U.image (fun x => -x)) :=
      Finset.disjoint_of_subset_left hUT
        (Finset.disjoint_of_subset_right (Finset.image_subset_image hUT) hdisj)
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · exact hUG h
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h; exact hneg y (hUG hy)
    · intro z hz
      rw [Finset.mem_union] at hz ⊢
      rcases hz with h | h
      · right; exact Finset.mem_image_of_mem _ h
      · left; rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h; rwa [neg_neg]
    · rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ neg_injective, hUcard]; ring
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSG, hClosed, _⟩ := hS
    show (S ∩ T) ∪ (S ∩ T).image (fun x => -x) = S
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · exact (Finset.mem_inter.mp h).1
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
        exact hClosed y (Finset.mem_inter.mp hy).1
    · intro x hx
      have hmem : x ∈ T ∪ T.image (fun x => -x) := hcov ▸ hSG hx
      rw [Finset.mem_union] at hmem
      rcases hmem with hT | hiT
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hT⟩)
      · rw [Finset.mem_image] at hiT; obtain ⟨y, hy, rfl⟩ := hiT
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, ?_, rfl⟩)
        exact Finset.mem_inter.mpr ⟨by have := hClosed (-y) hx; rwa [neg_neg] at this, hy⟩
  · intro U hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUT, _⟩ := hU
    show (U ∪ U.image (fun x => -x)) ∩ T = U
    rw [Finset.union_inter_distrib_right]
    have h1 : U ∩ T = U := Finset.inter_eq_left.mpr hUT
    have h2 : U.image (fun x => -x) ∩ T = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty]
      exact Finset.disjoint_of_subset_left (Finset.image_subset_image hUT) hdisj.symm
    rw [h1, h2, Finset.union_empty]


/-- Size-two specialization of `negClosed_subset_count_of_no_fintype`: there is one antipodal
pair for each transversal element, so the count is `|G|/2`, with no ambient `[Fintype F]`. -/
theorem negClosed_two_subset_count_of_no_fintype (G : Finset F) (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hneg : ∀ z ∈ G, -z ∈ G) :
    (G.powerset.filter (fun S => (∀ z ∈ S, -z ∈ S) ∧ S.card = 2)).card = G.card / 2 := by
  simpa using negClosed_subset_count_of_no_fintype G h2 h0 hneg 1

/-- Size-four specialization of `negClosed_subset_count_of_no_fintype`: the count is
`choose(|G|/2,2)`, with no ambient `[Fintype F]`. -/
theorem negClosed_four_subset_count_of_no_fintype (G : Finset F) (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hneg : ∀ z ∈ G, -z ∈ G) :
    (G.powerset.filter (fun S => (∀ z ∈ S, -z ∈ S) ∧ S.card = 4)).card
      = Nat.choose (G.card / 2) 2 := by
  simpa using negClosed_subset_count_of_no_fintype G h2 h0 hneg 2

/-- Size-six specialization of `negClosed_subset_count_of_no_fintype`: the count is
`choose(|G|/2,3)`, with no ambient `[Fintype F]`.  This is the exact subset-multiplicity
specialization used by the E3 top stratum. -/
theorem negClosed_six_subset_count_of_no_fintype (G : Finset F) (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hneg : ∀ z ∈ G, -z ∈ G) :
    (G.powerset.filter (fun S => (∀ z ∈ S, -z ∈ S) ∧ S.card = 6)).card
      = Nat.choose (G.card / 2) 3 := by
  simpa using negClosed_subset_count_of_no_fintype G h2 h0 hneg 3

/-- Corollary: `|G|` is even (`2 ∣ |G|`) for a negation-closed `G` with `0 ∉ G` over a field of
characteristic `≠ 2`, with **no `[Fintype F]`**. -/
theorem two_dvd_card_of_no_fintype (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    2 ∣ G.card := by
  obtain ⟨T, _, _, _, hcard⟩ := exists_neg_transversal_of_no_fintype G h2 h0 hneg
  exact ⟨T.card, by omega⟩

end ArkLib.ProximityGap.Frontier.AntipodalTransversalFintypeFree

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.AntipodalTransversalFintypeFree.exists_neg_transversal_of_no_fintype
#print axioms
  ArkLib.ProximityGap.Frontier.AntipodalTransversalFintypeFree.negClosed_subset_count_of_no_fintype
#print axioms
  ArkLib.ProximityGap.Frontier.AntipodalTransversalFintypeFree.negClosed_six_subset_count_of_no_fintype
