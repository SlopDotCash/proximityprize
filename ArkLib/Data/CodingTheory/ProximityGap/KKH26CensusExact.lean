/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26StratifiedSpread

/-!
# The exact bad-scalar census (#357 promotion 2: S1+N2 census exactness)

`KKH26StratifiedSpread.lean` proved the stratified LOWER bound: above the threshold
`p > s^{s/2}`, the number of distinct `r`-element subgroup sums is at least
`∑_j 2^{r−2j}·C(s/2, r−2j)`.  The zero-slack probe (`probe_n2_zero_slack.py`) measured
EQUALITY at every fully-testable scale.  This file proves the measured half — the
UPPER bound — and it turns out to be **unconditional** (no threshold, any prime, any
`r`): pure counting, no number theory.

The mechanism: write an `r`-subset of the order-`2^m` subgroup by exponents
`I ⊆ [0, 2^m)`, split `I` into the low half `C₀ ⊆ [0, n)` and the shifted high half
`C₁ ⊆ [0, n)` (`n := 2^{m−1}`).  Since `g^n = −1`,

    ∑_{i∈I} g^i = ∑_{C₀} g^c − ∑_{C₁} g^c = ∑_{C₀∖C₁} g^c − ∑_{C₁∖C₀} g^c
                = sVal g (C₀ △ C₁, C₀ ∖ C₁),

the common part `C₀ ∩ C₁` cancelling (those are exactly the antipodal pairs).  The
signed datum has support size `r − 2·|C₀∩C₁|` and its stratum is feasible because
`r − j = |C₀ ∪ C₁| ≤ n`.  So **every census value is a stratified signed value**:

* `census_card_le_stratified` — `#census ≤ ∑_j 2^{r−2j}·C(s/2, r−2j)`, unconditional;
* `census_card_eq_stratified` — **equality above the threshold** (with the landed
  lower bound `kkh26_stratified_count`): the antipodal stratification classifies ALL
  collisions; the in-tree ceiling numerator is *exact* for this construction class.

This discharges the campaign's promotion 2 (the S1/N2 zero-slack verdict, now a
theorem) and makes the KKH26-family ceiling census-extremal: no strictly better
numerator exists within the class.
-/

open Finset

namespace ArkLib.ProximityGap.KKH26

/-- **The census upper bound (unconditional).**  Every distinct `r`-element subgroup
sum is a stratified signed value, so the census is at most the stratified count —
for every prime `p`, every `r`, no threshold. -/
theorem census_card_le_stratified {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (r : ℕ) :
    ((((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x).card
      ≤ ∑ j ∈ feasSet (2 ^ (m - 1)) r, 2 ^ (r - 2 * j) * (2 ^ (m - 1)).choose (r - 2 * j) := by
  classical
  set n := 2 ^ (m - 1) with hn
  have h2n : 2 ^ m = 2 * n := by
    rw [hn, ← pow_succ']
    congr 1
    omega
  have hgneg : g ^ n = -1 := pow_half_eq_neg_one hm hg
  have hginj : Set.InjOn (fun i => g ^ i) ↑(range (2 ^ m)) := by
    intro a ha b hb hab
    exact hg.pow_inj (by simpa using ha) (by simpa using hb) hab
  rw [← card_stratData]
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_image_le (s := stratData n r) (f := sVal g))
  intro v hv
  obtain ⟨S, hS, hSsum⟩ := Finset.mem_image.mp hv
  obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
  -- recover the exponent set
  set I : Finset ℕ := (range (2 ^ m)).filter (fun i => g ^ i ∈ S) with hI
  have hIimg : I.image (fun i => g ^ i) = S := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hSsub hx)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩
  have hIinj : Set.InjOn (fun i => g ^ i) ↑I := fun a ha b hb hab =>
    hginj (Finset.mem_coe.mpr (Finset.filter_subset _ _ (Finset.mem_coe.mp ha)))
      (Finset.mem_coe.mpr (Finset.filter_subset _ _ (Finset.mem_coe.mp hb))) hab
  have hIcard : I.card = r := by
    rw [← hScard, ← hIimg]
    exact (Finset.card_image_of_injOn hIinj).symm
  have hIsum : v = ∑ i ∈ I, g ^ i := by
    rw [← hSsum, ← hIimg, Finset.sum_image hIinj]
  -- split into low and shifted-high halves
  set C0 : Finset ℕ := I.filter (fun i => i < n) with hC0
  set C1 : Finset ℕ := (I.filter (fun i => ¬ i < n)).image (fun i => i - n) with hC1
  have hC0sub : C0 ⊆ range n := by
    intro c hc
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hc).2
  have hsubinj : Set.InjOn (fun i => i - n) ↑(I.filter (fun i => ¬ i < n)) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    have hab' : a - n = b - n := hab
    omega
  have hC1sub : C1 ⊆ range n := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    have h1 : ¬ i < n := (Finset.mem_filter.mp hi).2
    have hiI : i ∈ I := Finset.filter_subset _ I hi
    have h2 : i < 2 ^ m := Finset.mem_range.mp (Finset.mem_filter.mp hiI).1
    exact Finset.mem_range.mpr (by omega)
  have hcards : C0.card + C1.card = r := by
    rw [hC1, Finset.card_image_of_injOn hsubinj, hC0]
    rw [← hIcard]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  -- the sum identity: v = ∑_{C0} g^c − ∑_{C1} g^c
  have hsplit : v = (∑ c ∈ C0, g ^ c) - ∑ c ∈ C1, g ^ c := by
    rw [hIsum, ← Finset.sum_filter_add_sum_filter_not I (fun i => i < n)]
    have h1 : ∑ i ∈ I.filter (fun i => ¬ i < n), g ^ i = ∑ c ∈ C1, g ^ (c + n) := by
      rw [hC1, Finset.sum_image hsubinj]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := (Finset.mem_filter.mp hi).2
      congr 1
      omega
    have h2 : ∑ c ∈ C1, g ^ (c + n) = -∑ c ∈ C1, g ^ c := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [pow_add, hgneg]
      ring
    rw [h1, h2, hC0]
    ring
  -- cancellation: subtract the common part
  set W : Finset ℕ := C0 ∩ C1 with hW
  have hcancel : v = (∑ c ∈ C0 \ C1, g ^ c) - ∑ c ∈ C1 \ C0, g ^ c := by
    rw [hsplit]
    have e0 : ∑ c ∈ C0 ∩ C1, g ^ c + ∑ c ∈ C0 \ C1, g ^ c = ∑ c ∈ C0, g ^ c :=
      Finset.sum_inter_add_sum_diff C0 C1 _
    have e1 : ∑ c ∈ C1 ∩ C0, g ^ c + ∑ c ∈ C1 \ C0, g ^ c = ∑ c ∈ C1, g ^ c :=
      Finset.sum_inter_add_sum_diff C1 C0 _
    rw [← e0, ← e1, Finset.inter_comm C1 C0]
    ring
  -- the signed datum
  set U : Finset ℕ := (C0 \ C1) ∪ (C1 \ C0) with hU
  set T : Finset ℕ := C0 \ C1 with hT
  have hdisj : Disjoint (C0 \ C1) (C1 \ C0) :=
    disjoint_sdiff_sdiff
  have hUT : U \ T = C1 \ C0 := by
    rw [hU, hT, Finset.union_sdiff_cancel_left hdisj]
  have hval : v = sVal g ⟨U, T⟩ := by
    rw [sVal, hUT, hT, hcancel]
  -- cardinalities
  have hjle0 : W.card ≤ C0.card := Finset.card_le_card Finset.inter_subset_left
  have hjle1 : W.card ≤ C1.card := Finset.card_le_card Finset.inter_subset_right
  have hc0d : (C0 \ C1).card = C0.card - W.card := by
    have := Finset.card_sdiff_add_card_inter C0 C1
    rw [hW]
    omega
  have hc1d : (C1 \ C0).card = C1.card - W.card := by
    have := Finset.card_sdiff_add_card_inter C1 C0
    rw [hW, Finset.inter_comm C0 C1]
    omega
  have hUcard : U.card = r - 2 * W.card := by
    rw [hU, Finset.card_union_of_disjoint hdisj, hc0d, hc1d]
    omega
  have hunion : (C0 ∪ C1).card ≤ n := by
    calc (C0 ∪ C1).card ≤ (range n).card :=
          Finset.card_le_card (Finset.union_subset hC0sub hC1sub)
      _ = n := Finset.card_range n
  have hrj : r - W.card ≤ n := by
    have := Finset.card_union_add_card_inter C0 C1
    rw [← hW] at this
    omega
  -- feasibility and membership
  have hfeas : W.card ∈ feasSet n r := mem_feasSet.mpr ⟨by omega, by omega⟩
  have hsig : (⟨U, T⟩ : (_ : Finset ℕ) × Finset ℕ) ∈ sigData n (r - 2 * W.card) := by
    refine mem_sigData.mpr ⟨⟨?_, hUcard⟩, ?_⟩
    · rw [hU]
      exact Finset.union_subset (Finset.Subset.trans Finset.sdiff_subset hC0sub)
        (Finset.Subset.trans Finset.sdiff_subset hC1sub)
    · rw [hU, hT]
      exact Finset.subset_union_left
  refine Finset.mem_image.mpr ⟨⟨U, T⟩, ?_, hval.symm⟩
  exact mem_stratData.mpr ⟨W.card, hfeas, hsig⟩

/-- **The exact census (promotion 2, S1+N2).**  Above the [KKH26] threshold the
number of distinct `r`-element subgroup sums EQUALS the stratified count: the
antipodal stratification classifies all collisions, and the in-tree ceiling numerator
is exact for this construction class. -/
theorem census_card_eq_stratified {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p) (r : ℕ) :
    ((((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x).card
      = ∑ j ∈ feasSet (2 ^ (m - 1)) r, 2 ^ (r - 2 * j) * (2 ^ (m - 1)).choose (r - 2 * j) :=
  le_antisymm (census_card_le_stratified hm hg r)
    (kkh26_stratified_count hm hg hp r)

end ArkLib.ProximityGap.KKH26

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.census_card_le_stratified
#print axioms ArkLib.ProximityGap.KKH26.census_card_eq_stratified
