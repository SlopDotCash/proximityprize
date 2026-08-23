/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.FisherLevelLocked
import ArkLib.Data.CodingTheory.ProximityGap.SubJohnsonListDischarge

/-!
# The Fisher list cap, INSTANTIATED on the Reed-Solomon code (#444, the named-but-unproven
`listCap_Fisher`)

`FisherPastJohnsonCap` proves the abstract set-system bound and DESCRIBES, in its docstring, a
`listCap_Fisher` "coding-theory phrasing", but never states it as a theorem. This file supplies that
instantiation: it feeds the deployed pairwise-intersection cap of the Reed-Solomon code
(`SubJohnsonListDischarge.rsCode_pairwise_agree_le`: two distinct degree-`<k` codewords agree on
`≤ k−1` points) into the level-locked Fisher bound to get the past-Johnson RS list cap directly.

## What is proved (all axiom-clean)

Working with `bigAgreeCodewords dom k m w` (the degree-`<k` codewords agreeing with the center word
`w` on `≥ k+m+1` points, from `SubJohnsonListSupply`):

* **`bigAgree_listAgreeSet_pairwise_inter_le`**: the agreement-sets-with-`w` of two DISTINCT
  codewords in the list intersect in `≤ k−1` points. (A point where both agree with `w` is a point
  where they agree with EACH OTHER, so the intersection embeds in their `≤ k−1` mutual-agreement
  set.)

* **`listAgreeSet_injOn_bigAgree`**: `c ↦ listAgreeSet c w` is INJECTIVE on `bigAgreeCodewords`
  when `k ≥ 1`: two codewords with the same `≥ k+m+1 ≥ k` agreement set coincide
  (`explainer_unique`).
  Hence the realized list size equals the cardinality of the agreement-set family.

* **`rs_listCap_Fisher`** (THE INSTANTIATION): for `k ≥ 1` (the divisor `C(k+m+1, k)` is
  automatically positive since `k ≤ k+m+1`, and the optimal counting level is `a+1 = k`),

  > `(bigAgreeCodewords dom k m w).card · C(k+m+1, k) ≤ C(n, k)`,

  i.e. the past-Johnson RS list at agreement radius `k+m+1` has size
  `≤ C(n, k) / C(k+m+1, k)`. This is the deployed Fisher cap with `t = k+m+1`, `a = k-1`, counted at
  the optimal level `a + 1 = k` (by `level_cap_monotone` from `FisherLevelLocked`). It is valid past
  the Johnson radius (where the second-moment denominator vanishes), and the saturation witness
  (`FisherLevelLocked.fisher_cap_saturated_n8`) shows it is met with EQUALITY by a real thin-`μ_n`
  family. The list count is governed purely by the RS min-distance `a = k-1`; the prize-relevant
  `μ_n` √-cancellation enters NOWHERE in this combinatorial bound.

## Scope (rules 1, 3, 5, 6, honesty contract)

Field-universal: the only code-specific input is the RS pairwise-agreement cap `k-1` (the min
distance), so this holds for ANY code with distance `≥ n-(k-1)`, INDEPENDENT of the domain's
thickness. NOT a CORE proof, NOT thinness-essential. It makes the docstring-named
`listCap_Fisher` an
actual theorem on the RS list, at the optimal counting level, and (with the saturation witness)
records that this combinatorial handle is exhausted: it is Johnson-radius-valid but cannot itself
reach the beyond-Johnson `δ*` margin, which is carried by the `μ_n` √-cancellation. CORE
`M(μ_n) ≤ C·√(n log(p/n))` stays OPEN. Makes NO asymptotic/capacity claim (cliff-at-n/2 untouched).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Pairwise agreement-set intersection cap.**  For two DISTINCT codewords `c, c'` in
`bigAgreeCodewords dom k m w`, their agreement-sets-with-`w` intersect in `≤ k − 1` points: a point
in both `listAgreeSet c w` and `listAgreeSet c' w` is a point where `c` and `c'` BOTH equal `w`,
hence agree with each other, so it lies in their `≤ k − 1` mutual-agreement set
(`rsCode_pairwise_agree_le`). -/
theorem bigAgree_listAgreeSet_pairwise_inter_le (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    (w : Fin n → F) {c c' : Fin n → F}
    (hc : c ∈ bigAgreeCodewords dom k m w) (hc' : c' ∈ bigAgreeCodewords dom k m w)
    (hne : c ≠ c') :
    (listAgreeSet c w ∩ listAgreeSet c' w).card ≤ k - 1 := by
  classical
  rw [bigAgreeCodewords, Finset.mem_filter] at hc hc'
  -- the mutual-agreement set of c, c'
  have hsub : listAgreeSet c w ∩ listAgreeSet c' w
      ⊆ Finset.univ.filter (fun x => c x = c' x) := by
    intro x hx
    rw [Finset.mem_inter, listAgreeSet, listAgreeSet, Finset.mem_filter, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx.1.2.trans hx.2.2.symm⟩
  exact le_trans (Finset.card_le_card hsub) (rsCode_pairwise_agree_le dom hk hc.2.1 hc'.2.1 hne)

open Classical in
/-- **The agreement-set map is injective on the list.**  When `k ≥ 1`, `c ↦ listAgreeSet c w` is
injective on `bigAgreeCodewords dom k m w`: two codewords sharing the same `≥ k+m+1 ≥ k` agreement
set agree with `w` on `≥ k` points, hence (`explainer_unique`) coincide. -/
theorem listAgreeSet_injOn_bigAgree (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k) (w : Fin n → F) :
    Set.InjOn (fun c => listAgreeSet c w) (bigAgreeCodewords dom k m w : Set (Fin n → F)) := by
  classical
  intro c hc c' hc' heq
  simp only at heq
  rw [Finset.mem_coe, bigAgreeCodewords, Finset.mem_filter] at hc hc'
  -- T := the common agreement set; |T| ≥ k+m+1 ≥ k; both agree with w on T
  set T := listAgreeSet c w with hT
  have hTcard : k ≤ T.card := le_trans (by omega) hc.2.2
  have hcag : ∀ i ∈ T, c i = w i := by
    intro i hi; rw [hT, listAgreeSet, Finset.mem_filter] at hi; exact hi.2
  have hc'ag : ∀ i ∈ T, c' i = w i := by
    intro i hi
    have : i ∈ listAgreeSet c' w := heq ▸ hi
    rw [listAgreeSet, Finset.mem_filter] at this; exact this.2
  exact explainer_unique dom hk hTcard hc.2.1 hc'.2.1 hcag hc'ag

open Classical in
/-- **`listCap_Fisher` on the Reed-Solomon code (the named instantiation).**  For `m + 2 ≤ k`
(so the band threshold `t = k+m+1` exceeds the optimal counting level `k = a+1`, `a = k-1`) and
`k ≥ 1`, the past-Johnson RS list at agreement radius `k+m+1` satisfies
`(bigAgreeCodewords dom k m w).card · C(k+m+1, k) ≤ C(n, k)`. This is the level-locked Fisher cap
(`card_le_choose_div_choose_at_level` at the optimal level `k = a+1`), instantiated with the RS
min-distance pairwise cap `a = k-1`. -/
theorem rs_listCap_Fisher (dom : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k)
    (w : Fin n → F) :
    (bigAgreeCodewords dom k m w).card * ((k + m + 1).choose k)
      ≤ (Fintype.card (Fin n)).choose k := by
  classical
  -- the agreement-set family F := image of bigAgreeCodewords under c ↦ listAgreeSet c w
  set Fam := (bigAgreeCodewords dom k m w).image (fun c => listAgreeSet c w) with hFam
  -- |Fam| = list size (injectivity)
  have hcardFam : Fam.card = (bigAgreeCodewords dom k m w).card := by
    rw [hFam, Finset.card_image_of_injOn]
    exact (listAgreeSet_injOn_bigAgree dom hk w)
  -- each member has card ≥ t = k+m+1
  have hsize : ∀ S ∈ Fam, k + m + 1 ≤ S.card := by
    intro S hS
    rw [hFam, Finset.mem_image] at hS
    obtain ⟨c, hc, rfl⟩ := hS
    rw [bigAgreeCodewords, Finset.mem_filter] at hc
    exact hc.2.2
  -- pairwise intersections ≤ a = k-1
  have hinter : ∀ S ∈ Fam, ∀ S' ∈ Fam, S ≠ S' → (S ∩ S').card ≤ k - 1 := by
    intro S hS S' hS' hne
    rw [hFam, Finset.mem_image] at hS hS'
    obtain ⟨c, hc, rfl⟩ := hS
    obtain ⟨c', hc', rfl⟩ := hS'
    have hcne : c ≠ c' := fun h => hne (by rw [h])
    exact bigAgree_listAgreeSet_pairwise_inter_le dom hk w hc hc' hcne
  -- apply the level-locked Fisher bound at the optimal level k = (k-1)+1
  have hak : k - 1 < k := by omega
  have hbound := Round11Fisher.card_le_choose_div_choose_at_level
    Fam (k + m + 1) (k - 1) k hsize hinter hak
  rwa [hcardFam] at hbound

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.bigAgree_listAgreeSet_pairwise_inter_le
#print axioms ProximityGap.Ownership.listAgreeSet_injOn_bigAgree
#print axioms ProximityGap.Ownership.rs_listCap_Fisher
