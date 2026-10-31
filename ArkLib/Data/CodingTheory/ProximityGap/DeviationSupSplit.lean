/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SparseDeviationExtremality

/-!
# The deviation-sup split: `ε_mca ≤ max(1/q, deviation-family sup)` (#357 capstone)

`SparseDeviationExtremality.lean` proved that any stack with two bad scalars is a
`(3δ, 2δ)`-deviation stack.  This file packages that into the consumable form: the
supremum defining `ε_mca` splits —

    ε_mca(C, δ) ≤ max( 1/q , sup over deviation-bounded stacks of the bad-mass ).

Every term of the `ε_mca` supremum either has at most one bad scalar (probability
mass `≤ 1/q`, below `ε* = 2^{-128}` at deployed fields) or its stack satisfies
`DeviationBounded` and its term is dominated by the restricted supremum.  Composed
with `le_mcaDeltaStar_of_good` (`MCADeltaStarSandwich.lean`), any upper bound on the
deviation-family bad-mass at radius `δ` immediately becomes `δ ≤ mcaDeltaStar`.
This file is the verified interface through which any future bound on the deviation
family reaches δ\*.

## Useful range and degeneracy

The split is valid for every `δ`, but the restriction to "almost-codeword pairs" is
only a genuine restriction for small `δ`.  The thresholds are truncated `ℝ≥0`
subtractions: `1 − 3δ` truncates to `0` once `δ ≥ 1/3`, and `1 − 2δ` once `δ ≥ 1/2`.
For `δ ≥ 1/2` both thresholds are `0`, so zero codewords with empty witness sets show
that **every** stack is `DeviationBounded` (`deviationBounded_of_half_le`), and the
restricted supremum is the full `ε_mca` supremum (`deviationSup_eq_epsMCA_of_half_le`):
the split then gives no localization and no new bound.  For `1/3 ≤ δ < 1/2` only the
`u₁` condition restricts.  In particular at rate `ρ ≤ 1/4` the whole beyond-Johnson
window `δ ∈ (1 − √ρ, 1 − ρ)` starts at or above `1/2`, exactly where the restriction is
vacuous, so this file does **not** reduce those windows to a structurally smaller
family; there the extremal count is the unrestricted `ε_mca` problem.  The earlier
claim that "the lower bracket of δ\* is formally a statement about almost-codeword
pairs only" holds only for `δ < 1/2` (and is substantive only well below that).
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.SparseDeviation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- A stack is **`δ`-deviation-bounded** if both rows agree with codewords on the
sparse-deviation thresholds of `rows_close_of_two_bad`: `u₁` on `≥ (1−2δ)·n`
positions, `u₀` on `≥ (1−3δ)·n`. -/
def DeviationBounded (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : Prop :=
  (∃ d ∈ (C : Set (ι → A)), ∃ W : Finset ι,
    (W.card : ℝ≥0) ≥ (1 - δ - δ) * Fintype.card ι ∧ ∀ i ∈ W, d i = u₁ i) ∧
  (∃ e ∈ (C : Set (ι → A)), ∃ V : Finset ι,
    (V.card : ℝ≥0) ≥ (1 - (δ + δ) - δ) * Fintype.card ι ∧ ∀ i ∈ V, e i = u₀ i)

open Classical in
/-- **The deviation-sup split.**  The `ε_mca` supremum is dominated by the maximum of
the single-scalar floor `1/q` and the supremum restricted to deviation-bounded
stacks.  Hence every upper bound on the deviation family's bad-mass is an upper
bound on `ε_mca` up to `1/q` — the formal interface between the sparse-deviation
reduction and the δ\* sandwich.  For `δ ≥ 1/2` the restriction is vacuous
(`deviationSup_eq_epsMCA_of_half_le`), so the split is informative only for `δ < 1/2`. -/
theorem epsMCA_le_max_deviationSup (C : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤
      max ((1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
        (⨆ u : Code.WordStack A (Fin 2) ι,
          if DeviationBounded C δ (u 0) (u 1) then
            Pr_{let γ ← $ᵖ F}[mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ]
          else 0) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  by_cases hdb : DeviationBounded C δ (u 0) (u 1)
  · -- deviation-bounded: dominated by the restricted sup
    refine le_max_of_le_right ?_
    refine le_trans ?_ (le_iSup (fun u' : Code.WordStack A (Fin 2) ι =>
      if DeviationBounded C δ (u' 0) (u' 1) then
        Pr_{let γ ← $ᵖ F}[mcaEvent (C : Set (ι → A)) δ (u' 0) (u' 1) γ]
      else 0) u)
    rw [if_pos hdb]
  · -- not deviation-bounded: by rows_close_of_two_bad, at most ONE bad scalar
    refine le_max_of_le_left ?_
    have hone : ∀ γ γ' : F, mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ →
        mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ' → γ = γ' := by
      intro γ γ' h h'
      by_contra hne
      exact hdb (rows_close_of_two_bad C hne h h')
    -- the bad set is a subsingleton, so its mass is ≤ 1/q
    rw [prob_uniform_eq_card_filter_div_card]
    have hcard : (Finset.univ.filter
        (fun γ : F => mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro γ hγ γ' hγ'
      exact hone γ γ' (Finset.mem_filter.mp hγ).2 (Finset.mem_filter.mp hγ').2
    calc ((Finset.univ.filter
          (fun γ : F => mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ)).card : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞)
        ≤ (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
          gcongr
          exact_mod_cast hcard
      _ = (1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := rfl

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **Degeneracy for `δ ≥ 1/2`.**  Both truncated thresholds `1 − 2δ` and `1 − 3δ` are `0`,
so the zero codeword with an empty witness set satisfies both clauses: every stack is
deviation-bounded. -/
theorem deviationBounded_of_half_le (C : Submodule F (ι → A)) {δ : ℝ≥0} (hδ : 1 / 2 ≤ δ)
    (u₀ u₁ : ι → A) : DeviationBounded C δ u₀ u₁ := by
  have h2 : (1 : ℝ≥0) ≤ δ + δ := by
    calc (1 : ℝ≥0) = 1 / 2 + 1 / 2 := (add_halves 1).symm
      _ ≤ δ + δ := add_le_add hδ hδ
  have hW : (1 - δ - δ : ℝ≥0) = 0 := tsub_eq_zero_of_le (tsub_le_iff_right.mpr h2)
  have hV : (1 - (δ + δ) - δ : ℝ≥0) = 0 := by rw [tsub_eq_zero_of_le h2, zero_tsub]
  have h0 : (0 : ι → A) ∈ (C : Set (ι → A)) := SetLike.mem_coe.mpr C.zero_mem
  refine ⟨⟨0, h0, ∅, ?_, fun i hi => by simp at hi⟩, ⟨0, h0, ∅, ?_, fun i hi => by simp at hi⟩⟩
  · rw [hW, zero_mul]; exact zero_le
  · rw [hV, zero_mul]; exact zero_le

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
open Classical in
/-- **The restricted supremum is all of `ε_mca` for `δ ≥ 1/2`.**  Hence
`epsMCA_le_max_deviationSup` gives no localization in that regime. -/
theorem deviationSup_eq_epsMCA_of_half_le (C : Submodule F (ι → A)) {δ : ℝ≥0}
    (hδ : 1 / 2 ≤ δ) :
    (⨆ u : Code.WordStack A (Fin 2) ι,
        if DeviationBounded C δ (u 0) (u 1) then
          Pr_{let γ ← $ᵖ F}[mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ]
        else 0) =
      epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  unfold epsMCA
  refine iSup_congr fun u => ?_
  rw [if_pos (deviationBounded_of_half_le C hδ (u 0) (u 1))]

end ProximityGap.SparseDeviation

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SparseDeviation.epsMCA_le_max_deviationSup
#print axioms ProximityGap.SparseDeviation.deviationBounded_of_half_le
#print axioms ProximityGap.SparseDeviation.deviationSup_eq_epsMCA_of_half_le
