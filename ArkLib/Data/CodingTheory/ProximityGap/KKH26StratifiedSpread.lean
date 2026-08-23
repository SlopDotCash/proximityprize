/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread

/-!
# KKH26 stratified spread — the exact-decomposition upgrade of [KKH26] Lemma 1 (issue #334)

This file upgrades the in-tree [KKH26] Lemma 1 (`kkh26_lemma1` in
`KKH26SumsOfRootsOfUnity.lean`) to its **stratified** form, hypothesis A2 of the issue #334
δ*-residuals program.

[KKH26] Lemma 1 counts only the *sign-free* sums of `r` distinct elements of the order-`s`
subgroup `G = ⟨g⟩ ⊆ F_p^×` (`s = 2^m`, `p > s^{s/2}`): subsets `S ⊆ G` with `S ∩ (−S) = ∅`,
yielding `≥ 2^r · (s/2).choose r` distinct sums.  But an arbitrary `r`-subset of `G`
decomposes uniquely as `j` antipodal pairs `{x, −x}` (which sum to `0`) plus a sign-free
remainder of `r − 2j` elements.  The numerical probe `probe_kkh26_stratified_spread.py`
(12/12 cells at `s ∈ {8, 16}`, `p` just above `s^{s/2}`) confirmed that the resulting
stratification is **exact and disjoint**: the set of `r`-sums is the disjoint union over the
feasible strata `j` of the sign-free `(r − 2j)`-sum sets, so

  `#{r-sums} = ∑_{j feasible} 2^{r−2j} · (s/2).choose (r−2j)`,

where stratum `j` is feasible iff `2j ≤ r` and `(r − 2j) + j ≤ s/2` (the sign-free part uses
`r − 2j` of the `s/2` antipodal classes and the `j` pairs use `j` further classes).  This file
proves the lower-bound half of that identity:

* **cross-stratum distinctness** (`sVal_inj_cross_strata`): two signed sums built from
  supports of *different* cardinalities `r₁ ≠ r₂` (both `≤ s/2`) are distinct in `F_p`, by
  the same resultant skeleton as the in-tree Lemma 1 — the difference of the two
  sum-polynomials is nonzero (it would otherwise force equal supports, hence `r₁ = r₂`), has
  at most `r₁ + r₂ ≤ s` coefficients `±1` on the window `[0, s/2)`, so the in-tree
  archimedean core `not_isRoot_of_l1On_pow_lt` applies at the *same* threshold `p > s^{s/2}`;
* **stratum realization** (`exists_realizing_subset`): every sign-free `(r − 2j)`-sum value is
  the sum of an honest `r`-element subset of `G`, obtained by adjoining `j` antipodal pairs on
  fresh classes (the feasibility predicate is exactly what makes the fresh classes exist);
* **the stratified count** (`kkh26_stratified_count`): for *every* `r` (no `r ≤ s/2`
  restriction — the feasibility predicate handles the bookkeeping, and the bound is
  nonvacuous for all `r ≤ s`),

    `∑_{j ∈ feasSet (s/2) r} 2^{r−2j} · (s/2).choose (r−2j) ≤ #{r-sums}`;

  the `j = 0` term alone is the [KKH26] Lemma 1 bound when `r ≤ s/2`
  (`lemma1_bound_le_stratified`), so this is a strict-for-`r ≥ 2` upgrade, and for
  `s/2 < r ≤ s` it gives an exponential count where Lemma 1 gives nothing;
* **the upgraded consumers** (`kkh26_stratified_epsMCA_lower_bound`,
  `kkh26_stratified_mcaDeltaStar_le`): the bad-line construction of
  `KKH26WitnessSpread.lean` is generic in the subset `T ⊆ G` (the bad-scalar identity
  `λ_T = −∑_{a∈T} a` and the fiber witness never use sign-freeness), so the `ε_mca` lower
  bound and the `δ*` upper bracket re-run with the bigger numerator — and with the radius
  hypothesis **relaxed** from `r ≤ s/2` to `r ≤ s`, pushing the bracket
  `mcaDeltaStar ≤ 1 − r/2^μ` below `1/2`.

Sanity anchors from the probe, kernel-checked below by `decide`: at `(s, r) = (8, 4)` the
stratified sum is `16 + 24 + 1 = 41` (vs. Lemma 1's `16`), and at `(s, r) = (8, 6)` it is
`24 + 1 = 25` (vs. Lemma 1: vacuous).

## Main results

* `feasSet` / `stratData` — the feasible strata and the stratified signed-data index set.
* `sVal_inj_cross_strata` — cross-stratum injectivity of signed sums at the threshold
  `p > s^{s/2}` (subsumes the in-tree `sVal_injOn` as the diagonal `r₁ = r₂`).
* `kkh26_stratified_count` — **the stratified spread count**, the headline of this file.
* `kkh26_stratified_epsMCA_lower_bound`, `kkh26_stratified_mcaDeltaStar_le` — the upgraded
  witness-spread consumers, with relaxed radius `r ≤ 2^μ`.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782.
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, ePrint 2020/654.
-/

open Polynomial Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ArkLib.ProximityGap.KKH26

/-! ### Feasible strata and the stratified data set -/

/-- The feasible strata for `r`-subsets of the order-`2n` subgroup with `n` antipodal
classes: stratum `j` (the number of antipodal pairs) is feasible iff the pair count fits
(`2j ≤ r`) and the `r − 2j` sign-free classes plus `j` pair classes fit among the `n`
classes (`(r − 2j) + j ≤ n`). -/
def feasSet (n r : ℕ) : Finset ℕ :=
  (range (r + 1)).filter fun j => 2 * j ≤ r ∧ r - 2 * j + j ≤ n

lemma mem_feasSet {n r j : ℕ} :
    j ∈ feasSet n r ↔ 2 * j ≤ r ∧ r - 2 * j + j ≤ n := by
  simp only [feasSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by omega, h⟩

/-- The stratified signed-data index set: the disjoint union over feasible strata `j` of the
sign-free signed data at `r − 2j` terms ([KKH26] equation (2), stratified). -/
def stratData (n r : ℕ) : Finset ((_ : Finset ℕ) × Finset ℕ) :=
  (feasSet n r).biUnion fun j => sigData n (r - 2 * j)

lemma mem_stratData {n r : ℕ} {d : (_ : Finset ℕ) × Finset ℕ} :
    d ∈ stratData n r ↔ ∃ j ∈ feasSet n r, d ∈ sigData n (r - 2 * j) := by
  simp [stratData]

/-- The strata are pairwise disjoint (a signed datum records its support cardinality). -/
lemma sigData_strata_disjoint {n r : ℕ} :
    ∀ j₁ ∈ feasSet n r, ∀ j₂ ∈ feasSet n r, j₁ ≠ j₂ →
      Disjoint (sigData n (r - 2 * j₁)) (sigData n (r - 2 * j₂)) := by
  intro j₁ hj₁ j₂ hj₂ hne
  obtain ⟨h21, -⟩ := mem_feasSet.mp hj₁
  obtain ⟨h22, -⟩ := mem_feasSet.mp hj₂
  rw [Finset.disjoint_left]
  intro d hd₁ hd₂
  have hc₁ := (mem_sigData.mp hd₁).1.2
  have hc₂ := (mem_sigData.mp hd₂).1.2
  omega

/-- The stratified data set has exactly `∑_j 2^{r−2j} · n.choose (r−2j)` elements. -/
lemma card_stratData (n r : ℕ) :
    (stratData n r).card
      = ∑ j ∈ feasSet n r, 2 ^ (r - 2 * j) * n.choose (r - 2 * j) := by
  classical
  rw [stratData, Finset.card_biUnion sigData_strata_disjoint]
  exact Finset.sum_congr rfl fun j _ => card_sigData _ _

/-- The `j = 0` stratum alone is the [KKH26] Lemma 1 count: the stratified sum dominates
`2^r · n.choose r` whenever `r ≤ n`. -/
lemma lemma1_bound_le_stratified {n r : ℕ} (hr : r ≤ n) :
    2 ^ r * n.choose r
      ≤ ∑ j ∈ feasSet n r, 2 ^ (r - 2 * j) * n.choose (r - 2 * j) := by
  have h0 : 0 ∈ feasSet n r := mem_feasSet.mpr (by omega)
  have h := Finset.single_le_sum
    (f := fun j => 2 ^ (r - 2 * j) * n.choose (r - 2 * j))
    (fun j _ => Nat.zero_le _) h0
  simpa using h

/-- Probe anchor `(s, r) = (8, 4)`: strata `j = 0, 1, 2` give `16 + 24 + 1 = 41`
(the in-tree Lemma 1 bound is `2^4 · C(4,4) = 16`). -/
example : ∑ j ∈ feasSet 4 4, 2 ^ (4 - 2 * j) * Nat.choose 4 (4 - 2 * j) = 41 := by decide

/-- Probe anchor `(s, r) = (8, 6)` — beyond the Lemma 1 range `r ≤ s/2`: strata
`j = 2, 3` give `24 + 1 = 25` (Lemma 1 is vacuous here). -/
example : ∑ j ∈ feasSet 4 6, 2 ^ (6 - 2 * j) * Nat.choose 4 (6 - 2 * j) = 25 := by decide

/-! ### Cross-stratum injectivity

The one new resultant step: signed sums with supports of *different* cardinalities are still
distinct at the same threshold `p > s^{s/2}`, because the collision polynomial
`R = P₁ − P₂` has window ℓ¹-norm `≤ r₁ + r₂ ≤ s` (instead of `2r ≤ s` on the diagonal), and
`R = 0` would force equal supports termwise, hence `r₁ = r₂`. -/

/-- **Cross-stratum injectivity of signed sums.**  Above the explicit threshold
`p > (2^m)^{2^{m-1}} = s^{s/2}`, signed data with supports of any cardinalities
`r₁, r₂ ≤ s/2` give equal values only if they are equal — in particular, sums from
*different* strata (`r₁ ≠ r₂`) are distinct.  The in-tree `sVal_injOn` is the diagonal
`r₁ = r₂` case. -/
theorem sVal_inj_cross_strata {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p) {r₁ r₂ : ℕ}
    (hr₁ : r₁ ≤ 2 ^ (m - 1)) (hr₂ : r₂ ≤ 2 ^ (m - 1))
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r₁) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r₂)
    (heq : sVal g d₁ = sVal g d₂) : d₁ = d₂ := by
  classical
  obtain ⟨U₁, T₁⟩ := d₁
  obtain ⟨U₂, T₂⟩ := d₂
  obtain ⟨⟨hU₁, hc₁⟩, hT₁⟩ := mem_sigData.mp hd₁
  obtain ⟨⟨hU₂, hc₂⟩, hT₂⟩ := mem_sigData.mp hd₂
  have hhalf : 0 < 2 ^ (m - 1) := by positivity
  by_cases hR : sumPoly U₁ T₁ - sumPoly U₂ T₂ = 0
  · obtain ⟨hU, hT⟩ := sumPoly_inj hT₁ hT₂ (sub_eq_zero.mp hR)
    subst hU; subst hT; rfl
  · exfalso
    -- the collision polynomial has `g` as a root
    have hroot : ((sumPoly U₁ T₁ - sumPoly U₂ T₂).map
        (Int.castRingHom (ZMod p))).IsRoot g := by
      rw [IsRoot.def, Polynomial.map_sub, eval_sub, sub_eq_zero,
        ← sVal_eq_eval g U₁ T₁, ← sVal_eq_eval g U₂ T₂]
      exact heq
    -- degree and ℓ¹ bookkeeping: at most `r₁ + r₂ ≤ 2^m` nonzero `±1` coefficients
    have hdegR : (sumPoly U₁ T₁ - sumPoly U₂ T₂).natDegree < 2 ^ (m - 1) :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (max_lt (sumPoly_natDegree_lt hhalf hU₁ hT₁) (sumPoly_natDegree_lt hhalf hU₂ hT₂))
    have hl1 : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ≤ r₁ + r₂ := by
      have h := l1On_sub_le (2 ^ (m - 1)) (sumPoly U₁ T₁) (sumPoly U₂ T₂)
      rw [l1On_sumPoly hU₁ hT₁, l1On_sumPoly hU₂ hT₂, hc₁, hc₂] at h
      omega
    have hsum2 : r₁ + r₂ ≤ 2 ^ m := by
      have hsum : 2 ^ (m - 1) * 2 = 2 ^ m := by
        rw [← pow_succ, Nat.sub_add_cancel hm]
      omega
    have hpow : l1On (2 ^ (m - 1)) (sumPoly U₁ T₁ - sumPoly U₂ T₂) ^ 2 ^ (m - 1) < p :=
      lt_of_le_of_lt (Nat.pow_le_pow_left (le_trans hl1 hsum2) _) hp
    exact not_isRoot_of_l1On_pow_lt hm hg hR hdegR hpow hroot

/-- Cross-stratum **distinctness**: sign-free sums with different numbers of terms
`r₁ ≠ r₂` (both `≤ s/2`) are distinct elements of `F_p`. -/
theorem sVal_ne_cross_strata {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p) {r₁ r₂ : ℕ}
    (hr₁ : r₁ ≤ 2 ^ (m - 1)) (hr₂ : r₂ ≤ 2 ^ (m - 1)) (hne : r₁ ≠ r₂)
    {d₁ d₂ : (_ : Finset ℕ) × Finset ℕ}
    (hd₁ : d₁ ∈ sigData (2 ^ (m - 1)) r₁) (hd₂ : d₂ ∈ sigData (2 ^ (m - 1)) r₂) :
    sVal g d₁ ≠ sVal g d₂ := by
  intro heq
  have hdd := sVal_inj_cross_strata hm hg hp hr₁ hr₂ hd₁ hd₂ heq
  apply hne
  rw [← (mem_sigData.mp hd₁).1.2, ← (mem_sigData.mp hd₂).1.2, hdd]

/-! ### Stratum realization

Every sign-free `(r − 2j)`-sum value is realized by an `r`-element subset of `G`: adjoin
`j` antipodal pairs `{g^w, −g^w}` on classes `w` fresh from the sign-free support.  The
pairs each sum to `0`, so the subset sum is unchanged.  Feasibility
`(r − 2j) + j ≤ s/2` is exactly the existence of the `j` fresh classes. -/

/-- **Stratum realization.**  For a feasible stratum `j` and a signed datum `d` at
`r − 2j` terms, some `r`-element subset of `G = {g^i : i < 2^m}` sums to `sVal g d`. -/
lemma exists_realizing_subset {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) {r j : ℕ}
    (hj2 : 2 * j ≤ r) (hjfit : r - 2 * j + j ≤ 2 ^ (m - 1))
    {d : (_ : Finset ℕ) × Finset ℕ} (hd : d ∈ sigData (2 ^ (m - 1)) (r - 2 * j)) :
    ∃ S ∈ ((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r,
      ∑ x ∈ S, x = sVal g d := by
  classical
  obtain ⟨U, T⟩ := d
  obtain ⟨⟨hU, hc⟩, hT⟩ := mem_sigData.mp hd
  have hsum2 : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  -- choose `j` antipodal classes fresh from the sign-free support `U`
  have hjle : j ≤ (range (2 ^ (m - 1)) \ U).card := by
    rw [Finset.card_sdiff_of_subset hU, card_range, hc]; omega
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hjle
  have hWfacts : ∀ w ∈ W, w < 2 ^ (m - 1) ∧ w ∉ U := by
    intro w hw
    have h := hWsub hw
    rw [Finset.mem_sdiff, Finset.mem_range] at h
    exact h
  have hUlt : ∀ a ∈ U, a < 2 ^ (m - 1) := fun a ha => mem_range.mp (hU ha)
  have hinj_add : Function.Injective (fun i : ℕ => i + 2 ^ (m - 1)) :=
    fun a b h => by simpa using h
  -- the exponent set: sign-free part `T ∪ (U∖T + s/2)` plus pairs `W ∪ (W + s/2)`
  set B : Finset ℕ := (U \ T).image (fun i => i + 2 ^ (m - 1)) with hBdef
  set D : Finset ℕ := W.image (fun i => i + 2 ^ (m - 1)) with hDdef
  set E : Finset ℕ := (T ∪ B) ∪ (W ∪ D) with hEdef
  -- pairwise disjointness of the four exponent blocks
  have hTB : Disjoint T B := by
    rw [Finset.disjoint_left]
    intro a haT haB
    rw [hBdef, Finset.mem_image] at haB
    obtain ⟨u, -, hue⟩ := haB
    have h1 := hUlt a (hT haT)
    omega
  have hWD : Disjoint W D := by
    rw [Finset.disjoint_left]
    intro a haW haD
    rw [hDdef, Finset.mem_image] at haD
    obtain ⟨w, -, hwe⟩ := haD
    have h1 := (hWfacts a haW).1
    omega
  have hTBWD : Disjoint (T ∪ B) (W ∪ D) := by
    rw [Finset.disjoint_left]
    intro a ha haWD
    rcases Finset.mem_union.mp ha with haT | haB
    · rcases Finset.mem_union.mp haWD with haW | haD
      · exact (hWfacts a haW).2 (hT haT)
      · rw [hDdef, Finset.mem_image] at haD
        obtain ⟨w, -, hwe⟩ := haD
        have h1 := hUlt a (hT haT)
        omega
    · rcases Finset.mem_union.mp haWD with haW | haD
      · rw [hBdef, Finset.mem_image] at haB
        obtain ⟨u, -, hue⟩ := haB
        have h1 := (hWfacts a haW).1
        omega
      · rw [hBdef, Finset.mem_image] at haB
        rw [hDdef, Finset.mem_image] at haD
        obtain ⟨u, hu, hue⟩ := haB
        obtain ⟨w, hw, hwe⟩ := haD
        have huw : u = w := by omega
        subst huw
        exact (hWfacts u hw).2 (Finset.mem_sdiff.mp hu).1
  -- the exponent set has exactly `r` elements
  have hcardB : B.card = (U \ T).card := Finset.card_image_of_injective _ hinj_add
  have hcardD : D.card = j := by
    rw [hDdef, Finset.card_image_of_injective _ hinj_add, hWcard]
  have hcardUT : (U \ T).card + T.card = r - 2 * j := by
    rw [Finset.card_sdiff_add_card_eq_card hT, hc]
  have hcardE : E.card = r := by
    rw [hEdef, Finset.card_union_of_disjoint hTBWD, Finset.card_union_of_disjoint hTB,
      Finset.card_union_of_disjoint hWD, hcardB, hcardD, hWcard]
    omega
  -- the exponent set lives in the window `[0, 2^m)`
  have hEsub : E ⊆ range (2 ^ m) := by
    intro a ha
    rw [hEdef] at ha
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp ha with h1 | h1
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · have := hUlt a (hT h2); omega
      · rw [hBdef, Finset.mem_image] at h2
        obtain ⟨u, hu, hue⟩ := h2
        have := hUlt u (Finset.mem_sdiff.mp hu).1
        omega
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · have := (hWfacts a h2).1; omega
      · rw [hDdef, Finset.mem_image] at h2
        obtain ⟨w, hw, hwe⟩ := h2
        have := (hWfacts w hw).1
        omega
  -- exponentiation is injective on the window
  have hginj : ∀ a ∈ E, ∀ b ∈ E, g ^ a = g ^ b → a = b := by
    intro a ha b hb hab
    exact hg.pow_inj (mem_range.mp (hEsub ha)) (mem_range.mp (hEsub hb)) hab
  refine ⟨E.image (fun i => g ^ i), ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨Finset.image_subset_image hEsub, ?_⟩
    have hinjOn : Set.InjOn (fun i => g ^ i) ↑E := fun a ha b hb hab =>
      hginj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
    rw [Finset.card_image_of_injOn hinjOn]
    exact hcardE
  · -- the sum: the `j` pairs cancel, leaving the signed sum
    rw [Finset.sum_image hginj, hEdef, Finset.sum_union hTBWD, Finset.sum_union hTB,
      Finset.sum_union hWD]
    have hBsum : ∑ b ∈ B, g ^ b = -∑ u ∈ U \ T, g ^ u := by
      rw [hBdef, Finset.sum_image (fun a _ b _ h => hinj_add h), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [pow_add, pow_half_eq_neg_one hm hg, mul_neg_one]
    have hDsum : ∑ b ∈ D, g ^ b = -∑ w ∈ W, g ^ w := by
      rw [hDdef, Finset.sum_image (fun a _ b _ h => hinj_add h), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [pow_add, pow_half_eq_neg_one hm hg, mul_neg_one]
    rw [hBsum, hDsum]
    simp only [sVal]
    ring

/-! ### The stratified count -/

/-- **The stratified spread count** (hypothesis A2 of issue #334, upgrading [KKH26]
Lemma 1).  Let `g ∈ F_p` be a primitive `2^m`-th root of unity (so `G = {g^i : i < 2^m}`
has order `s = 2^m`) and suppose `p > s^{s/2}`.  Then for **every** `r`, the set of sums of
`r` distinct elements of `G` has at least

  `∑_{j ∈ feasSet (s/2) r} 2^{r−2j} · (s/2).choose (r−2j)`

elements — one stratum per feasible number `j` of antipodal pairs.  The `j = 0` term is the
[KKH26] Lemma 1 bound (`lemma1_bound_le_stratified`), so this strictly improves Lemma 1 for
`2 ≤ r ≤ s/2` and is the *only* nonvacuous bound for `s/2 < r ≤ s`. -/
theorem kkh26_stratified_count {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) {g : ZMod p}
    (hg : IsPrimitiveRoot g (2 ^ m)) (hp : ((2 : ℕ) ^ m) ^ 2 ^ (m - 1) < p) (r : ℕ) :
    ∑ j ∈ feasSet (2 ^ (m - 1)) r, 2 ^ (r - 2 * j) * (2 ^ (m - 1)).choose (r - 2 * j) ≤
      ((((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x).card := by
  classical
  -- cross- and intra-stratum injectivity of the value map on the stratified data
  have hinj : Set.InjOn (sVal g) ↑(stratData (2 ^ (m - 1)) r) := by
    intro d₁ hd₁ d₂ hd₂ heq
    obtain ⟨j₁, hj₁, hd₁'⟩ := mem_stratData.mp (Finset.mem_coe.mp hd₁)
    obtain ⟨j₂, hj₂, hd₂'⟩ := mem_stratData.mp (Finset.mem_coe.mp hd₂)
    obtain ⟨h21, hf1⟩ := mem_feasSet.mp hj₁
    obtain ⟨h22, hf2⟩ := mem_feasSet.mp hj₂
    exact sVal_inj_cross_strata hm hg hp (by omega) (by omega) hd₁' hd₂' heq
  -- every stratified value is an honest `r`-subset sum
  have hsub : (stratData (2 ^ (m - 1)) r).image (sVal g) ⊆
      (((range (2 ^ m)).image (fun i => g ^ i)).powersetCard r).image
        fun S => ∑ x ∈ S, x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, hd'⟩ := mem_stratData.mp hd
    obtain ⟨hj2, hjfit⟩ := mem_feasSet.mp hj
    obtain ⟨S, hS, hSsum⟩ := exists_realizing_subset hm hg hj2 hjfit hd'
    exact Finset.mem_image.mpr ⟨S, hS, hSsum⟩
  calc ∑ j ∈ feasSet (2 ^ (m - 1)) r, 2 ^ (r - 2 * j) * (2 ^ (m - 1)).choose (r - 2 * j)
      = ((stratData (2 ^ (m - 1)) r).image (sVal g)).card := by
        rw [Finset.card_image_of_injOn hinj, card_stratData]
    _ ≤ _ := Finset.card_le_card hsub

/-! ### The upgraded witness-spread consumers

The bad-line construction of `KKH26WitnessSpread.lean` is generic in the subset `T ⊆ G`:
`badline_pointwise_agreement` takes an arbitrary `T : Finset (ZMod p)` with `|T| ≥ 2`, and
the bad scalar is the generic coefficient identity `λ_T = −∑_{a∈T} a`.  So the consumers
re-run verbatim with the stratified count — and with the radius hypothesis relaxed from
`r ≤ 2^{μ−1}` to `r ≤ 2^μ` (only `δ = 1 − r/2^μ ≥ 0` is needed downstream; `fiber_count`
and `kkh26_ca_failure` impose no upper bound on `r`). -/

/-- Injectivity of `i ↦ g^i` below the order of `g`, for nonzero `g` in a field (local copy
of the `private` helper in `KKH26WitnessSpread.lean`). -/
private lemma pow_inj_lt_orderOf {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

open Classical in
/-- **The stratified witness spread (`ε_mca` lower bound).**  For the explicit evaluation
code of degree ≤ `(r−2)m` on the smooth `n = 2^μ·m`-point domain `⟨g⟩ ⊆ F_p^×`, above the
explicit prime threshold `p > (2^μ)^{2^{μ−1}}`, and now for the **full radius range**
`2 ≤ r ≤ 2^μ`:

  `ε_mca(C, 1 − r/2^μ) ≥ (∑_{j feasible} 2^{r−2j}·(2^{μ−1}).choose (r−2j)) / p`.

This upgrades `kkh26_epsMCA_lower_bound` in both the numerator (stratified count, strictly
larger for `r ≥ 2`) and the range (`r ≤ 2^μ` instead of `r ≤ 2^{μ−1}`). -/
theorem kkh26_stratified_epsMCA_lower_bound {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ μ) :
    ((∑ j ∈ feasSet (2 ^ (μ - 1)) r,
        2 ^ (r - 2 * j) * (2 ^ (μ - 1)).choose (r - 2 * j) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
      ≤ epsMCA (F := ZMod p) (evalCode g n ((r - 2) * m))
          (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) := by
  classical
  subst hn
  -- basic positivity and order bookkeeping
  have hm0 : m ≠ 0 := by omega
  have hs1 : (1 : ℕ) ≤ 2 ^ μ := Nat.one_le_two_pow
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ (2 ^ μ * m) = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (Nat.mul_ne_zero (by positivity) hm0)] at h1
    exact zero_ne_one h1
  have hgmord : orderOf (g ^ m) = 2 ^ μ := by
    have h1 : (g ^ m) ^ (2 ^ μ) = 1 := by
      rw [← pow_mul, mul_comm m (2 ^ μ), ← hg]; exact pow_orderOf_eq_one g
    have h2 : orderOf (g ^ m) ∣ 2 ^ μ := orderOf_dvd_of_pow_eq_one h1
    have h3 : g ^ (m * orderOf (g ^ m)) = 1 := by
      rw [pow_mul]; exact pow_orderOf_eq_one (g ^ m)
    have h4 : 2 ^ μ * m ∣ m * orderOf (g ^ m) := hg ▸ orderOf_dvd_of_pow_eq_one h3
    rw [mul_comm (2 ^ μ) m] at h4
    have h5 : 2 ^ μ ∣ orderOf (g ^ m) :=
      (Nat.mul_dvd_mul_iff_left (by omega : 0 < m)).mp h4
    exact Nat.dvd_antisymm h2 h5
  have hprim : IsPrimitiveRoot (g ^ m) (2 ^ μ) := by
    have h := IsPrimitiveRoot.orderOf (g ^ m)
    rwa [hgmord] at h
  -- the stratified count: many distinct sums of r distinct elements of G = ⟨g^m⟩
  have hlem1 := kkh26_stratified_count hμ hprim hp r
  set Gsub : Finset (ZMod p) :=
    (Finset.range (2 ^ μ)).image (fun i => (g ^ m) ^ i) with hGsub
  set sums : Finset (ZMod p) :=
    (Gsub.powersetCard r).image (fun T => ∑ x ∈ T, x) with hsums
  -- the word stack of the bad line
  set u : WordStack (ZMod p) (Fin 2) (Fin (2 ^ μ * m)) :=
    ![fun i => (g ^ (i : ℕ)) ^ (r * m), fun i => (g ^ (i : ℕ)) ^ ((r - 1) * m)] with hu
  -- the bad-scalar set
  set Λ : Finset (ZMod p) := sums.image (fun w => -w) with hΛ
  have hΛcard : (∑ j ∈ feasSet (2 ^ (μ - 1)) r,
      2 ^ (r - 2 * j) * (2 ^ (μ - 1)).choose (r - 2 * j)) ≤ Λ.card := by
    rw [hΛ, Finset.card_image_of_injective _ neg_injective]
    exact hlem1
  -- every λ ∈ Λ is a bad scalar: mcaEvent fires with the fiber witness
  have hbad : ∀ γ ∈ Λ, mcaEvent (evalCode g (2 ^ μ * m) ((r - 2) * m))
      (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) (u 0) (u 1) γ := by
    intro γ hγ
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨T, hT, hTsum⟩ := Finset.mem_image.mp hw
    obtain ⟨hTG, hTcard⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨q, hqdeg, hqagree⟩ :=
      badline_pointwise_agreement hm T (by omega : 2 ≤ T.card)
    rw [hTcard] at hqdeg hqagree
    -- the fiber witness set, at index level
    set S : Finset (Fin (2 ^ μ * m)) :=
      Finset.univ.filter (fun i => (g ^ (i : ℕ)) ^ m ∈ T) with hSdef
    -- index-level and domain-level fibers have the same cardinality
    have himg : (Finset.univ : Finset (Fin (2 ^ μ * m))).image
          (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))
        = (Finset.range (2 ^ μ * m)).image (fun i => g ^ i) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨(i : ℕ), Finset.mem_range.mpr i.isLt, rfl⟩
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, rfl⟩
    have hSimg : S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))
        = ((Finset.range (2 ^ μ * m)).image (fun i => g ^ i)).filter
            (fun x => x ^ m ∈ T) := by
      rw [← himg, Finset.filter_image]
    have hScard : S.card = m * r := by
      have h1 : (S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))).card = S.card :=
        Finset.card_image_of_injOn (fun i _ j _ hij =>
          Fin.ext (pow_inj_lt_orderOf hg0 hg _ i.isLt _ j.isLt hij))
      rw [← h1, hSimg, fiber_count hm hs1 hg T hTG, hTcard]
    refine ⟨S, ?_, ⟨fun i => q.eval (g ^ (i : ℕ)), ⟨q, hqdeg, fun _ => rfl⟩, ?_⟩, ?_⟩
    · -- |S| ≥ (1 − δ)·n
      have hcardF : (Fintype.card (Fin (2 ^ μ * m)) : ℝ≥0) = ((2 ^ μ * m : ℕ) : ℝ≥0) := by
        rw [Fintype.card_fin]
      have hrs1 : (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have h : (r : ℝ≥0) ≤ ((2 ^ μ : ℕ) : ℝ≥0) := by exact_mod_cast hr
        simpa [Nat.cast_pow] using h
      have h1δ : (1 : ℝ≥0) - (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ))
          = (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := tsub_tsub_cancel_of_le hrs1
      rw [hScard, hcardF, h1δ]
      have harith : ((r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) * ((2 ^ μ * m : ℕ) : ℝ≥0)
          = ((m * r : ℕ) : ℝ≥0) := by
        push_cast
        rw [div_mul_eq_mul_div, mul_comm ((r : ℝ≥0)) _, mul_comm ((2 : ℝ≥0) ^ μ) _,
          mul_assoc, mul_div_assoc,
          mul_div_cancel_left₀ _ (by positivity : ((2 : ℝ≥0) ^ μ) ≠ 0)]
      rw [harith]
    · -- the line point agrees with the codeword on S
      intro i hi
      have hxm : (g ^ (i : ℕ)) ^ m ∈ T := (Finset.mem_filter.mp hi).2
      have hpt := hqagree (g ^ (i : ℕ)) hxm
      rw [hTsum] at hpt
      rw [hu]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
      linear_combination -hpt
    · -- no joint pair: the direction word is far (kkh26_ca_failure)
      rintro ⟨v₀, _, v₁, hv₁, hpair⟩
      obtain ⟨q₁, hq₁deg, hq₁⟩ := hv₁
      have hS'H : S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))
          ⊆ (Finset.range (2 ^ μ * m)).image (fun i => g ^ i) := by
        rw [hSimg]
        exact Finset.filter_subset _ _
      have hS'card : r * m ≤ (S.image (fun i : Fin (2 ^ μ * m) => g ^ (i : ℕ))).card := by
        rw [hSimg, fiber_count hm hs1 hg T hTG, hTcard, mul_comm]
      refine kkh26_ca_failure (g := g) (n := 2 ^ μ * m) hm hr2 _ hS'H hS'card q₁ hq₁deg ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have h1 : v₁ i = u 1 i := (hpair i hi).2
      have h2 : v₁ i = q₁.eval (g ^ (i : ℕ)) := hq₁ i
      rw [hu] at h1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      rw [← h2, h1]
  -- feed the spread into the in-tree lower-bound engine
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := ZMod p) (evalCode g (2 ^ μ * m) ((r - 2) * m))
    (1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)) u Λ hbad
  rw [ZMod.card p] at hengine
  refine le_trans ?_ hengine
  exact ENNReal.div_le_div_right (by exact_mod_cast hΛcard) _

open Classical in
/-- **The stratified `δ*` upper bracket.**  For any target error `ε*` strictly below the
stratified bad-scalar mass, the formal MCA threshold of the explicit smooth-domain
evaluation code is at most `1 − r/2^μ` — now for the full radius range `2 ≤ r ≤ 2^μ`, so
the bracket reaches all the way down to `δ = 0` (at `r = 2^μ` the numerator is still
`≥ 1`).  Upgrades `kkh26_mcaDeltaStar_le` for issue #334. -/
theorem kkh26_stratified_mcaDeltaStar_le {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ μ) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((∑ j ∈ feasSet (2 ^ (μ - 1)) r,
        2 ^ (r - 2 * j) * (2 ^ (μ - 1)).choose (r - 2 * j) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) :=
  ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _
    (lt_of_lt_of_le hεstar
      (kkh26_stratified_epsMCA_lower_bound hμ hm hn hg hp hr2 hr))

end ArkLib.ProximityGap.KKH26

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.sVal_inj_cross_strata
#print axioms ArkLib.ProximityGap.KKH26.sVal_ne_cross_strata
#print axioms ArkLib.ProximityGap.KKH26.exists_realizing_subset
#print axioms ArkLib.ProximityGap.KKH26.kkh26_stratified_count
#print axioms ArkLib.ProximityGap.KKH26.lemma1_bound_le_stratified
#print axioms ArkLib.ProximityGap.KKH26.kkh26_stratified_epsMCA_lower_bound
#print axioms ArkLib.ProximityGap.KKH26.kkh26_stratified_mcaDeltaStar_le
