/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeviationSupSplit
import ArkLib.Data.CodingTheory.ProximityGap.MCASyndromeFactorization
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactComputationKit

/-!
# The sparse-cover computable form: `ε_mca ≤ max(1/q, sparse-pair sweep / q)`

Support brick for the #357 exact-`δ*` programme, composing three landed engines:

* the **deviation-sup split** (`epsMCA_le_max_deviationSup`): the `ε_mca` sup is dominated
  by `max(1/q, sup over deviation-bounded stacks)` — stacks whose rows agree with codewords
  on `≥ (1−2δ)n` resp. `≥ (1−3δ)n` positions;
* the **translation law** (`stackProb_eq_of_sub_mem`): subtracting those codewords does not
  change the per-stack probability — so each deviation-bounded stack may be replaced by its
  pair of *deviations*, rows that **vanish on the same large sets**;
* the **exact-computation kit** (`prob_mcaEvent_eq_badScalarCount_div`): the per-stack value
  is the computable census `badScalarCount / q`.

The composition (`epsMCA_le_max_sparse_badScalarCount`):

  `ε_mca(C, δ) ≤ max( 1/q , (max badScalarCount over sparseRows(s₀) × sparseRows(s₁)) / q )`

where `sparseRows s` is the **explicit, decidable** `Finset` of rows vanishing on some set
of size `≥ s`, at `s₀ = ⌈(1−3δ)n⌉₊`, `s₁ = ⌈(1−2δ)n⌉₊`. For interior radii the sparse sets
are exponentially smaller than the `q^{n−k}` syndrome classes (rows of Hamming weight
`≤ 3δn` resp. `≤ 2δn`), so the upper-bound side of an exact rung becomes a small finite
sweep over almost-codeword deviations plus the `1/q` floor — the computational engine for
exact `ε_mca` upper bounds at the rungs beyond `n = 4` (the registered
monomial-orbit-extremality conjecture's falsifier (i)).

Everything here is unconditional; the `max` with `1/q` is exactly the price of the
sparse-deviation reduction (`rows_close_of_two_bad`: a stack with two bad scalars *must*
be deviation-bounded, so non-sparse stacks contribute at most one bad scalar).

## References
- [ABF26] ePrint 2026/680, Definition 4.3. Issue #357 (the exact-point programme;
  PROMOTION 1 / the deviation-sup capstone; N2).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.SparseCoverComputable

open ProximityGap.SparseDeviation ProximityGap.MCASyndromeFactorization
open ProximityGap.MCAExactKit

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The sparse-row sets -/

/-- The rows vanishing on some coordinate set of size `≥ s` — the explicit, decidable
deviation pool. (`s = ⌈(1−2δ)n⌉₊` ⟺ Hamming weight `≤ n − s ≈ 2δn`.) -/
def sparseRows (s : ℕ) : Finset (ι → A) :=
  Finset.univ.filter (fun r => ∃ W : Finset ι, s ≤ W.card ∧ ∀ i ∈ W, r i = 0)

theorem mem_sparseRows {s : ℕ} {r : ι → A} :
    r ∈ (sparseRows s : Finset (ι → A)) ↔ ∃ W : Finset ι, s ≤ W.card ∧ ∀ i ∈ W, r i = 0 := by
  simp [sparseRows]

/-! ## The sparse-cover bound, probability form -/

open Classical in
/-- **The sparse-cover bound.** The `ε_mca` sup is dominated by the `1/q` floor together
with the per-stack probabilities of **deviation pairs**: rows vanishing on `≥ s₀`- resp.
`≥ s₁`-sets, at the ceil thresholds of the deviation-sup split. -/
theorem epsMCA_le_max_sparse_sup (C : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤
      max ((1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
        (⨆ r₀ ∈ (sparseRows ⌈(1 - (δ + δ) - δ) * (Fintype.card ι : ℝ≥0)⌉₊ :
            Finset (ι → A)),
         ⨆ r₁ ∈ (sparseRows ⌈(1 - δ - δ) * (Fintype.card ι : ℝ≥0)⌉₊ :
            Finset (ι → A)),
          stackProb (F := F) C δ r₀ r₁) := by
  refine le_trans (epsMCA_le_max_deviationSup C δ) (max_le_max le_rfl ?_)
  refine iSup_le fun u => ?_
  by_cases hdb : DeviationBounded C δ (u 0) (u 1)
  · rw [if_pos hdb]
    obtain ⟨⟨d, hd, W, hW, hdW⟩, ⟨e, he, V, hV, heV⟩⟩ := hdb
    -- replace the stack by its deviation pair
    have heq : Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ]
        = stackProb (F := F) C δ (u 0 - e) (u 1 - d) := by
      have h₀ : u 0 - (u 0 - e) ∈ C := by
        have : u 0 - (u 0 - e) = e := by abel
        rw [this]; exact he
      have h₁ : u 1 - (u 1 - d) ∈ C := by
        have : u 1 - (u 1 - d) = d := by abel
        rw [this]; exact hd
      exact stackProb_eq_of_sub_mem C δ h₀ h₁
    rw [heq]
    refine le_iSup₂_of_le (u 0 - e) ?_ (le_iSup₂_of_le (u 1 - d) ?_ le_rfl)
    · exact mem_sparseRows.mpr
        ⟨V, Nat.ceil_le.mpr hV, fun i hi => by simp [heV i hi]⟩
    · exact mem_sparseRows.mpr
        ⟨W, Nat.ceil_le.mpr hW, fun i hi => by simp [hdW i hi]⟩
  · rw [if_neg hdb]
    exact zero_le _

/-! ## The computable form -/

open Classical in
/-- **The sparse-cover computable form.** With the integer-threshold bridge in force,
`ε_mca` is bounded by `max(1/q, M/q)` where `M` is the maximum bad-scalar census over the
explicit sparse-row pairs — a finite, decidable sweep over almost-codeword deviations. -/
theorem epsMCA_le_max_sparse_badScalarCount (C : Submodule F (ι → A))
    [DecidablePred (· ∈ (C : Set (ι → A)))] {δ : ℝ≥0} {t : ℕ}
    (ht : ∀ S : Finset ι,
      ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) ↔ t ≤ S.card) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤
      max ((1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
        ((((sparseRows ⌈(1 - (δ + δ) - δ) * (Fintype.card ι : ℝ≥0)⌉₊ :
              Finset (ι → A)).sup (fun r₀ =>
            (sparseRows ⌈(1 - δ - δ) * (Fintype.card ι : ℝ≥0)⌉₊ :
              Finset (ι → A)).sup (fun r₁ =>
              badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁)) : ℕ) : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞)) := by
  refine le_trans (epsMCA_le_max_sparse_sup C δ) (max_le_max le_rfl ?_)
  refine iSup₂_le fun r₀ hr₀ => iSup₂_le fun r₁ hr₁ => ?_
  have hPr : stackProb (F := F) C δ r₀ r₁
      = (badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁ : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) :=
    prob_mcaEvent_eq_badScalarCount_div (C : Set (ι → A)) ht r₀ r₁
  rw [hPr]
  gcongr
  exact_mod_cast le_trans
    (Finset.le_sup (f := fun r₁ =>
      badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁) hr₁)
    (Finset.le_sup (f := fun r₀ =>
      (sparseRows ⌈(1 - δ - δ) * (Fintype.card ι : ℝ≥0)⌉₊ : Finset (ι → A)).sup
        (fun r₁ => badScalarCount (F := F) (C : Set (ι → A)) t r₀ r₁)) hr₀)

/-! ## Source audit -/

#print axioms epsMCA_le_max_sparse_sup
#print axioms epsMCA_le_max_sparse_badScalarCount

end ProximityGap.SparseCoverComputable
