/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Sparse-deviation extremality (#357 promotion 1: the N1 mechanism, provable core)

The N1 maximizer audit found that every exact extremizer of `ε_mca` is a
sparse-deviation stack (an almost-codeword pair).  This file proves the mechanism —
with explicit constants, for every linear code, unconditionally:

**Two bad scalars force both rows close to the code.**  If `γ ≠ γ′` are both
`mcaEvent`-bad for `(u₀, u₁)` at radius `δ`, then differencing the two line
explanations on the overlap of their witnesses yields

  * `u₁` agrees with the codeword `(γ−γ′)⁻¹ • (w_γ − w_γ′)` on `≥ (1−2δ)·n` positions
    (`u1_close_of_two_bad`);
  * `u₀ = line_γ − γ·u₁` then agrees with `w_γ − γ·d` on `≥ (1−3δ)·n` positions
    (`u0_close_of_two_bad`);
  * both at once: `rows_close_of_two_bad`.

Hence every stack with at least two bad scalars is a `(3δ, 2δ)`-deviation stack, and
since single-bad-scalar stacks contribute at most `1/q` to `ε_mca`, the supremum
defining `ε_mca` — and with it the lower bracket of the δ* sandwich — is governed by
the `O(δ)`-neighborhood of codeword pairs.  This is the formal statement that the
threshold problem's search space is the sparse-deviation family: the N1 audit's
template, now a theorem about *all* contributing stacks, not just toy extremizers.

(The remaining half of promotion 1 — computing the extremal bad-mass *within* the
deviation family and locating its `ε*·q` crossing — is where the exact census
(`KKH26CensusExact.lean`) and the deviation-kernel theory (`Jo26DeviationKernels.lean`)
take over: those are the campaign's standing tools for exactly this family.)
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.SparseDeviation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Witness-overlap arithmetic (asymmetric radii): sets of relative size `1−α` and
`1−β` intersect in relative size `≥ 1−α−β` (trivial when `α+β ≥ 1`, by
inclusion–exclusion otherwise). -/
theorem card_inter_witnesses {α β : ℝ≥0} {T T' : Finset ι}
    (hT : (T.card : ℝ≥0) ≥ (1 - α) * Fintype.card ι)
    (hT' : (T'.card : ℝ≥0) ≥ (1 - β) * Fintype.card ι) :
    ((T ∩ T').card : ℝ≥0) ≥ (1 - α - β) * Fintype.card ι := by
  by_cases hαβ : (1 : ℝ≥0) ≤ α + β
  · rw [tsub_tsub, tsub_eq_zero_of_le hαβ, zero_mul]
    exact zero_le _
  · push Not at hαβ
    have hα1 : α ≤ 1 := le_of_lt (lt_of_le_of_lt (le_add_right le_rfl) hαβ)
    have hβ1 : β ≤ 1 := le_of_lt (lt_of_le_of_lt (le_add_left le_rfl) hαβ)
    have hkey : (1 - α - β) + 1 = (1 - α) + (1 - β) := by
      rw [tsub_tsub, tsub_add_eq_add_tsub (le_of_lt hαβ),
        tsub_add_tsub_comm hα1 hβ1]
    have hunion : ((T ∪ T').card : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) :=
      Nat.cast_le.mpr (Finset.card_le_univ _ |>.trans (le_of_eq Finset.card_univ))
    have hsum : (T.card : ℝ≥0) + (T'.card : ℝ≥0)
        = ((T ∪ T').card : ℝ≥0) + ((T ∩ T').card : ℝ≥0) := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ≥0))
        (Finset.card_union_add_card_inter T T').symm
    have hchain : (1 - α - β) * (Fintype.card ι : ℝ≥0) + (Fintype.card ι : ℝ≥0)
        ≤ ((T ∩ T').card : ℝ≥0) + (Fintype.card ι : ℝ≥0) := by
      calc (1 - α - β) * (Fintype.card ι : ℝ≥0) + (Fintype.card ι : ℝ≥0)
          = ((1 - α) + (1 - β)) * (Fintype.card ι : ℝ≥0) := by
            rw [← hkey, add_mul, one_mul]
        _ = (1 - α) * Fintype.card ι + (1 - β) * Fintype.card ι := add_mul _ _ _
        _ ≤ (T.card : ℝ≥0) + (T'.card : ℝ≥0) := add_le_add hT hT'
        _ = ((T ∪ T').card : ℝ≥0) + ((T ∩ T').card : ℝ≥0) := hsum
        _ ≤ (Fintype.card ι : ℝ≥0) + ((T ∩ T').card : ℝ≥0) := by gcongr
        _ = ((T ∩ T').card : ℝ≥0) + (Fintype.card ι : ℝ≥0) := add_comm _ _
    exact le_of_add_le_add_right hchain

/-- **Two bad scalars force the second row close.**  If `γ ≠ γ′` are both bad for
`(u₀, u₁)` at radius `δ` over a linear code, the difference of the two line
explanations exhibits a codeword agreeing with `u₁` on `≥ (1−δ−δ)·n` positions. -/
theorem u1_close_of_two_bad (C : Submodule F (ι → A)) {δ : ℝ≥0} {u₀ u₁ : ι → A}
    {γ γ' : F} (hne : γ ≠ γ')
    (h : mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)
    (h' : mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ') :
    ∃ d ∈ (C : Set (ι → A)), ∃ W : Finset ι,
      (W.card : ℝ≥0) ≥ (1 - δ - δ) * Fintype.card ι ∧ ∀ i ∈ W, d i = u₁ i := by
  obtain ⟨T, hTcard, ⟨w, hw, hwag⟩, -⟩ := h
  obtain ⟨T', hT'card, ⟨w', hw', hw'ag⟩, -⟩ := h'
  refine ⟨(γ - γ')⁻¹ • (w - w'), ?_, T ∩ T',
    card_inter_witnesses hTcard hT'card, ?_⟩
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hw hw')
  · intro i hi
    obtain ⟨hiT, hiT'⟩ := Finset.mem_inter.mp hi
    have hγγ' : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
    have hdiff : w i - w' i = (γ - γ') • u₁ i := by
      rw [hwag i hiT, hw'ag i hiT', sub_smul]
      abel
    calc ((γ - γ')⁻¹ • (w - w')) i = (γ - γ')⁻¹ • (w i - w' i) := rfl
      _ = (γ - γ')⁻¹ • ((γ - γ') • u₁ i) := by rw [hdiff]
      _ = u₁ i := by rw [smul_smul, inv_mul_cancel₀ hγγ', one_smul]

/-- **Two bad scalars force the first row close** (on the triple overlap,
`≥ (1−δ−δ−δ)·n` positions): `u₀ = line_γ − γ·u₁` agrees with `w_γ − γ·d`. -/
theorem u0_close_of_two_bad (C : Submodule F (ι → A)) {δ : ℝ≥0} {u₀ u₁ : ι → A}
    {γ γ' : F} (hne : γ ≠ γ')
    (h : mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)
    (h' : mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ') :
    ∃ e ∈ (C : Set (ι → A)), ∃ V : Finset ι,
      (V.card : ℝ≥0) ≥ (1 - (δ + δ) - δ) * Fintype.card ι ∧ ∀ i ∈ V, e i = u₀ i := by
  obtain ⟨d, hd, W, hWcard, hWag⟩ := u1_close_of_two_bad C hne h h'
  obtain ⟨T, hTcard, ⟨w, hw, hwag⟩, -⟩ := h
  have hWcard' : (W.card : ℝ≥0) ≥ (1 - (δ + δ)) * Fintype.card ι := by
    rwa [← tsub_tsub]
  refine ⟨w - γ • d, Submodule.sub_mem _ hw (Submodule.smul_mem _ _ hd),
    W ∩ T, card_inter_witnesses hWcard' hTcard, ?_⟩
  intro i hi
  obtain ⟨hiW, hiT⟩ := Finset.mem_inter.mp hi
  calc (w - γ • d) i = w i - γ • d i := rfl
    _ = (u₀ i + γ • u₁ i) - γ • u₁ i := by rw [hwag i hiT, hWag i hiW]
    _ = u₀ i := by abel

/-- **Sparse-deviation extremality (promotion 1, provable core).**  Every stack with
two distinct bad scalars at radius `δ` is a `(3δ, 2δ)`-deviation stack: both rows
agree with codewords outside `O(δ)·n` positions.  Single-bad-scalar stacks contribute
`≤ 1/q` to `ε_mca`, so the threshold problem's contributing stacks all live in the
`O(δ)`-neighborhood of codeword pairs — the N1 template, for every linear code. -/
theorem rows_close_of_two_bad (C : Submodule F (ι → A)) {δ : ℝ≥0} {u₀ u₁ : ι → A}
    {γ γ' : F} (hne : γ ≠ γ')
    (h : mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)
    (h' : mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ') :
    (∃ d ∈ (C : Set (ι → A)), ∃ W : Finset ι,
      (W.card : ℝ≥0) ≥ (1 - δ - δ) * Fintype.card ι ∧ ∀ i ∈ W, d i = u₁ i) ∧
    (∃ e ∈ (C : Set (ι → A)), ∃ V : Finset ι,
      (V.card : ℝ≥0) ≥ (1 - (δ + δ) - δ) * Fintype.card ι ∧ ∀ i ∈ V, e i = u₀ i) :=
  ⟨u1_close_of_two_bad C hne h h', u0_close_of_two_bad C hne h h'⟩

end ProximityGap.SparseDeviation

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SparseDeviation.card_inter_witnesses
#print axioms ProximityGap.SparseDeviation.u1_close_of_two_bad
#print axioms ProximityGap.SparseDeviation.rows_close_of_two_bad
