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
deviation-family bad-mass at radius `δ` immediately becomes `δ ≤ mcaDeltaStar`:
**the lower bracket of δ\* is now formally a statement about almost-codeword pairs
only.**  The extremal count over this family in the window is the problem's
irreducible open core; this file is the verified interface through which any future
bound on it reaches δ\*.
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
reduction and the δ\* sandwich. -/
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

end ProximityGap.SparseDeviation

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.SparseDeviation.epsMCA_le_max_deviationSup
