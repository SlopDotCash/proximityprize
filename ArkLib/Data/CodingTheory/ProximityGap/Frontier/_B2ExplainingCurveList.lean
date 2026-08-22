/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25SpreadBound

/-!
# B2 — the explaining-curve list bound (packing + uniqueness) (issue #466, lane W1)

**Where this sits.** The [GG25] (ePrint 2025/2054) Def 3.1 chain in-tree covers the
definition (`CurveDecodable`, `GG25CurveDecodability.lean`), the Lemma 3.2 spread bound
(`GG25SpreadBound.lean`), the Theorem 3.3 consumer (`GG25MCAFromCurveDecodability.lean`), the
[Jo26] §5 marked equivalence/interpolation/non-covering bricks, and the *input*-side pigeonhole
(`curveDecodable_of_curveListSize`: a small curve cover ⟹ decodability). What was missing is the
**output side**: nothing bounded *how many distinct codeword curves can each explain many close
seeds* — the "list size of curve decoding" that [GG25] uses implicitly when it speaks of *the*
explaining curve. This file supplies it, from one kernel fact:

* `stack_eq_of_curve_agree_card_gt` — **the determinacy kernel**: two degree-`ℓ` coefficient
  stacks whose curves agree (as words) at more than `ℓ` seeds are *equal* — coordinate-wise the
  difference is a degree-`≤ ℓ` vector polynomial with too many roots (reuses the
  `gdiff_zero_card_le` dual-separation root bound of `GG25SpreadBound`);
* `explainSet` — the seeds of the close set that a given stack explains (`f α` = its curve),
  so `CurveDecodable`'s conclusion is literally `b ≤ (explainSet δ u f cs).card`;
* `explainSet_inter_card_le` — distinct stacks share at most `ℓ` explained seeds;
* `explainerSet_card_mul_choose_le` — **the packing bound**: the stacks explaining `≥ b` seeds
  number at most `C(|A_δ|, ℓ+1) / C(b, ℓ+1)` (stated multiplied out, division-free): each such
  stack owns all `(ℓ+1)`-subsets of its explained set, and by the kernel these families are
  pairwise disjoint inside the `(ℓ+1)`-subsets of the close set;
* `explainerSet_card_le_div` — the divided form (`ℓ < b`);
* `explainer_unique` / `exists_unique_explainer_of_curveDecodable` — **uniqueness of the
  explaining curve**: as soon as `2b > |A_δ(u,f)| + ℓ`, at most one stack (codeword or not)
  explains `≥ b` seeds; combined with `CurveDecodable` this upgrades [GG25] Thm 3.3's
  "some codeword curve" to "*the* codeword curve". (Note `2b > |A_δ| + ℓ` together with any
  explainer forces `b > ℓ`, so the uniqueness regime is automatically the nontrivial one of
  [Jo26] Remark 5.3.)

**Honest scope.** Everything here is unconditional counting over an arbitrary `F`-module
alphabet; it does NOT produce curve decodability for any code — for explicit plain RS above
Johnson that *input* remains the open wall (`RSCurveListSizeResidual` / BCHKS Conj 1.12,
DISPROOF_LOG C43). This brick bounds and rigidifies the *output* list of the [GG25] engine.
Axiom-clean `[propext, Classical.choice, Quot.sound]`.

## References
* [GG25] Z. Guo, V. Guruswami, ePrint 2025/2054 (ECCC TR25-166), Def 3.1, Lemma 3.2, Thm 3.3.
* [Jo26] S. Jo, ePrint 2026/891, Def 2.7, §5. Issue #466 lane W1 (B2).
-/

open Finset Code
open scoped NNReal

namespace ProximityGap.B2ExplainList

open ProximityGap ProximityGap.GG25Lemma32

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### The determinacy kernel -/

/-- **The determinacy kernel.** Two degree-`ℓ` coefficient stacks whose curves agree, as words,
at more than `ℓ` seeds are equal. Coordinate-wise the difference `gdiff` is a vector polynomial
of degree `≤ ℓ` vanishing at every seed of `S`; the `GG25SpreadBound` dual-separation root
bound (`gdiff_zero_card_le`) caps its vanishing set at `ℓ` unless the coordinate never
disagrees. -/
theorem stack_eq_of_curve_agree_card_gt {ℓ : ℕ} {cs cs' : Fin (ℓ + 1) → ι → A}
    {S : Finset F} (hcard : ℓ < S.card)
    (hagree : ∀ α ∈ S, comb cs α = comb cs' α) : cs = cs' := by
  classical
  by_contra hne
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hne
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hj₀
  have hi : i₀ ∈ disagree cs cs' := by
    simp only [disagree, mem_filter, mem_univ, true_and]
    exact ⟨j₀, hi₀⟩
  have hsub : S ⊆ univ.filter (fun α : F => gdiff cs cs' i₀ α = 0) := by
    intro α hα
    simp only [mem_filter, mem_univ, true_and]
    rw [← comb_sub, hagree α hα, sub_self]
  have hle := Finset.card_le_card hsub
  have hbound := gdiff_zero_card_le (F := F) cs cs' hi
  omega

/-! ### The explained set of a stack -/

/-- **The explained set** of a coefficient stack `cs` on the instance `(u, f)`: the close seeds
`α ∈ A_δ(u, f)` at which `f α` *is* the curve of `cs`. `CurveDecodable`'s conclusion is
`b ≤ (explainSet δ u f cs).card` for some codeword stack `cs` (definitionally the same
filter). -/
noncomputable def explainSet (δ : ℝ≥0) {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → A)
    (f : F → ι → A) (cs : Fin (ℓ + 1) → ι → A) : Finset F :=
  (curveCloseSet δ u f).filter
    (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i)

theorem explainSet_subset_closeSet (δ : ℝ≥0) {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → A)
    (f : F → ι → A) (cs : Fin (ℓ + 1) → ι → A) :
    explainSet δ u f cs ⊆ curveCloseSet δ u f :=
  Finset.filter_subset _ _

/-- On its explained set, `f` equals the stack's curve. -/
theorem comb_eq_of_mem_explainSet {δ : ℝ≥0} {ℓ : ℕ} {u : Fin (ℓ + 1) → ι → A}
    {f : F → ι → A} {cs : Fin (ℓ + 1) → ι → A} {α : F}
    (hα : α ∈ explainSet δ u f cs) : f α = comb cs α :=
  (Finset.mem_filter.mp hα).2

/-- **Distinct stacks share at most `ℓ` explained seeds** (on a common explained seed the two
curves both equal `f α`, so `> ℓ` shared seeds would force the stacks equal by the kernel). -/
theorem explainSet_inter_card_le {δ : ℝ≥0} {ℓ : ℕ} {u : Fin (ℓ + 1) → ι → A}
    {f : F → ι → A} {cs cs' : Fin (ℓ + 1) → ι → A} (hne : cs ≠ cs') :
    (explainSet δ u f cs ∩ explainSet δ u f cs').card ≤ ℓ := by
  by_contra hgt
  push_neg at hgt
  refine hne (stack_eq_of_curve_agree_card_gt hgt (fun α hα => ?_))
  rw [Finset.mem_inter] at hα
  have h1 := comb_eq_of_mem_explainSet hα.1
  have h2 := comb_eq_of_mem_explainSet hα.2
  rw [← h1, ← h2]

/-! ### The packing bound -/

open Classical in
/-- **The explainer set**: all coefficient stacks (codeword-rowed or not) explaining at least
`b` close seeds of the instance `(u, f)`. -/
noncomputable def explainerSet (δ : ℝ≥0) {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → A)
    (f : F → ι → A) (b : ℕ) : Finset (Fin (ℓ + 1) → ι → A) :=
  univ.filter (fun cs => b ≤ (explainSet δ u f cs).card)

open Classical in
theorem mem_explainerSet {δ : ℝ≥0} {ℓ : ℕ} {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A}
    {b : ℕ} {cs : Fin (ℓ + 1) → ι → A} :
    cs ∈ explainerSet δ u f b ↔ b ≤ (explainSet δ u f cs).card := by
  simp [explainerSet]

/-- **The packing bound (division-free form).** The number of distinct stacks explaining `≥ b`
close seeds, times `C(b, ℓ+1)`, is at most `C(|A_δ(u,f)|, ℓ+1)`: each explainer owns every
`(ℓ+1)`-subset of its explained set; by the determinacy kernel no `(ℓ+1)`-subset is owned
twice; and all of them are `(ℓ+1)`-subsets of the close set. -/
theorem explainerSet_card_mul_choose_le (δ : ℝ≥0) {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → A)
    (f : F → ι → A) (b : ℕ) :
    (explainerSet δ u f b).card * b.choose (ℓ + 1)
      ≤ (curveCloseSet δ u f).card.choose (ℓ + 1) := by
  classical
  set E := explainerSet δ u f b with hE
  have hdisj : ∀ cs ∈ E, ∀ cs' ∈ E, cs ≠ cs' →
      Disjoint ((explainSet δ u f cs).powersetCard (ℓ + 1))
        ((explainSet δ u f cs').powersetCard (ℓ + 1)) := by
    intro cs _ cs' _ hne
    rw [Finset.disjoint_left]
    intro V hV hV'
    rw [Finset.mem_powersetCard] at hV hV'
    obtain ⟨hVsub, hVcard⟩ := hV
    obtain ⟨hV'sub, _⟩ := hV'
    have hcardV : ℓ < V.card := by omega
    refine hne (stack_eq_of_curve_agree_card_gt hcardV (fun α hα => ?_))
    have h1 := comb_eq_of_mem_explainSet (hVsub hα)
    have h2 := comb_eq_of_mem_explainSet (hV'sub hα)
    rw [← h1, ← h2]
  have hsub : E.biUnion (fun cs => (explainSet δ u f cs).powersetCard (ℓ + 1))
      ⊆ (curveCloseSet δ u f).powersetCard (ℓ + 1) := by
    rw [Finset.biUnion_subset]
    intro cs _
    exact Finset.powersetCard_mono (explainSet_subset_closeSet δ u f cs)
  calc E.card * b.choose (ℓ + 1)
      = ∑ _cs ∈ E, b.choose (ℓ + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ cs ∈ E, ((explainSet δ u f cs).powersetCard (ℓ + 1)).card := by
        refine Finset.sum_le_sum (fun cs hcs => ?_)
        rw [Finset.card_powersetCard]
        exact Nat.choose_le_choose _ (mem_explainerSet.mp hcs)
    _ = (E.biUnion (fun cs => (explainSet δ u f cs).powersetCard (ℓ + 1))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((curveCloseSet δ u f).powersetCard (ℓ + 1)).card := Finset.card_le_card hsub
    _ = (curveCloseSet δ u f).card.choose (ℓ + 1) := Finset.card_powersetCard _ _

/-- The divided form: in the nontrivial regime `ℓ < b` ([Jo26] Remark 5.3), the explainer
count is at most `C(|A_δ|, ℓ+1) / C(b, ℓ+1)` (Nat division). -/
theorem explainerSet_card_le_div (δ : ℝ≥0) {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → A)
    (f : F → ι → A) {b : ℕ} (hb : ℓ < b) :
    (explainerSet δ u f b).card
      ≤ (curveCloseSet δ u f).card.choose (ℓ + 1) / b.choose (ℓ + 1) := by
  have hpos : 0 < b.choose (ℓ + 1) := Nat.choose_pos (by omega)
  rw [Nat.le_div_iff_mul_le hpos]
  exact explainerSet_card_mul_choose_le δ u f b

/-! ### Uniqueness of the explaining curve -/

/-- **Uniqueness threshold.** If `2b > |A_δ(u,f)| + ℓ`, at most one stack explains `≥ b` close
seeds: two would overlap in `≥ 2b − |A_δ| > ℓ` seeds and be equal by the kernel. -/
theorem explainer_unique {δ : ℝ≥0} {ℓ : ℕ} {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A}
    {b : ℕ} (h2b : (curveCloseSet δ u f).card + ℓ < 2 * b)
    {cs cs' : Fin (ℓ + 1) → ι → A}
    (hb : b ≤ (explainSet δ u f cs).card) (hb' : b ≤ (explainSet δ u f cs').card) :
    cs = cs' := by
  by_contra hne
  have hinter := explainSet_inter_card_le (δ := δ) (u := u) (f := f) hne
  have hunion : (explainSet δ u f cs ∪ explainSet δ u f cs').card
      ≤ (curveCloseSet δ u f).card :=
    Finset.card_le_card (Finset.union_subset (explainSet_subset_closeSet δ u f cs)
      (explainSet_subset_closeSet δ u f cs'))
  have hsplit := Finset.card_union_add_card_inter
    (explainSet δ u f cs) (explainSet δ u f cs')
  omega

/-- **[GG25] Thm 3.3, uniqueness upgrade.** A `(ℓ, δ, a, b)`-curve-decodable code on an
instance whose close set reaches `a` but stays below `2b − ℓ` admits **the** explaining
codeword curve: it exists (decodability) and every stack explaining `≥ b` close seeds —
codeword-rowed or not — equals it. -/
theorem exists_unique_explainer_of_curveDecodable {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0}
    {a b : ℕ} (h : CurveDecodable (F := F) C ℓ δ a b)
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} (hf : ∀ α, f α ∈ C)
    (hclose : a ≤ (curveCloseSet δ u f).card)
    (h2b : (curveCloseSet δ u f).card + ℓ < 2 * b) :
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧ b ≤ (explainSet δ u f cs).card ∧
      ∀ cs' : Fin (ℓ + 1) → ι → A, b ≤ (explainSet δ u f cs').card → cs' = cs := by
  obtain ⟨cs, hcs, hcount⟩ := h u f hf hclose
  have hcount' : b ≤ (explainSet δ u f cs).card := hcount
  exact ⟨cs, hcs, hcount', fun cs' hcs' => explainer_unique h2b hcs' hcount'⟩

end ProximityGap.B2ExplainList

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.B2ExplainList.stack_eq_of_curve_agree_card_gt
#print axioms ProximityGap.B2ExplainList.explainSet_inter_card_le
#print axioms ProximityGap.B2ExplainList.explainerSet_card_mul_choose_le
#print axioms ProximityGap.B2ExplainList.explainerSet_card_le_div
#print axioms ProximityGap.B2ExplainList.explainer_unique
#print axioms ProximityGap.B2ExplainList.exists_unique_explainer_of_curveDecodable
