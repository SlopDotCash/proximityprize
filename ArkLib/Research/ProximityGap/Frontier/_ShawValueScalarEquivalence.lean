/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Shaw value scalar equivalence for the proximity-prize core (#444, door-(iv) Lane 2)

This file packages the citable scalar normalization behind Shaw's 2026-06-18 reduction:

* `M` is the worst-frequency coset-half / Gauss-period sup norm.
* the prize floor is `sqrt (n * log m)`, where `m = p / n` (morally `p/n`, index of the thin
  subgroup).
* the **Shaw value** is the dimensionless ratio

  `Sh(M,n,m) = M / sqrt (n * log m)`.

The machine-checked content is deliberately modest but useful: for `n > 0` and `m > 1`, a bound on
`M` at the prize floor is **definitionally equivalent** to a bound on the Shaw value, with the same
constant.  The family theorem is the exact formal form of

  `prize bound with an absolute constant`  iff  `Sh(n) = O(1)`.

## Honest scope

This proves no cancellation and gives no upper bound on the open scalar `M`; it only removes a layer
of normalization ambiguity from the door-(iv) reduction.  The open theorem remains an arithmetic
anti-concentration / monomial-sum evaluation for the actual worst frequency.  No moment route,
completion route, capacity claim, or thick-subgroup monotonicity is used.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence

open Real

/-- The dimensionless Shaw value: worst scalar divided by the prize floor. -/
noncomputable def shawValue (M n m : ℝ) : ℝ :=
  M / Real.sqrt (n * Real.log m)

/-- The scalar prize-floor bound with constant `C`. -/
def PrizeScalarBound (C M n m : ℝ) : Prop :=
  M ≤ C * Real.sqrt (n * Real.log m)

/-- The same bound after Shaw-value normalization. -/
noncomputable def ShawValueBound (C M n m : ℝ) : Prop :=
  shawValue M n m ≤ C

/-- Positivity of the prize floor in the thin-index regime `n > 0`, `m > 1`. -/
theorem prizeFloor_pos {n m : ℝ} (hn : 0 < n) (hm : 1 < m) :
    0 < Real.sqrt (n * Real.log m) := by
  apply Real.sqrt_pos.mpr
  exact mul_pos hn (Real.log_pos hm)

/-- **Scalar Shaw equivalence.** In the prize regime `n > 0`, `m > 1`, bounding the raw worst
scalar `M` by `C sqrt(n log m)` is equivalent to bounding the dimensionless Shaw value by `C`, with
no change of constants. -/
theorem shawValueBound_iff_prizeScalarBound {C M n m : ℝ} (hn : 0 < n) (hm : 1 < m) :
    ShawValueBound C M n m ↔ PrizeScalarBound C M n m := by
  unfold ShawValueBound PrizeScalarBound shawValue
  exact div_le_iff₀ (prizeFloor_pos hn hm)

/-- Forward direction: `Sh(M,n,m) ≤ C` gives the prize-floor scalar bound. -/
theorem prizeScalarBound_of_shawValueBound {C M n m : ℝ} (hn : 0 < n) (hm : 1 < m)
    (h : ShawValueBound C M n m) :
    PrizeScalarBound C M n m :=
  (shawValueBound_iff_prizeScalarBound hn hm).mp h

/-- Reverse direction: the prize-floor scalar bound gives `Sh(M,n,m) ≤ C`. -/
theorem shawValueBound_of_prizeScalarBound {C M n m : ℝ} (hn : 0 < n) (hm : 1 < m)
    (h : PrizeScalarBound C M n m) :
    ShawValueBound C M n m :=
  (shawValueBound_iff_prizeScalarBound hn hm).mpr h

/-- Uniform prize-floor boundedness for a family of instances. -/
def PrizeFamilyBound {ι : Type*} (M n m : ι → ℝ) : Prop :=
  ∃ C : ℝ, ∀ i : ι, PrizeScalarBound C (M i) (n i) (m i)

/-- Uniform Shaw-value boundedness, i.e. `Sh(n) = O(1)` in the scalar reduction. -/
noncomputable def ShawFamilyBound {ι : Type*} (M n m : ι → ℝ) : Prop :=
  ∃ C : ℝ, ∀ i : ι, ShawValueBound C (M i) (n i) (m i)

/-- **Family capstone: prize bound iff `Sh(n)=O(1)`.** For any family of thin instances with
`n_i > 0` and `m_i > 1`, a uniform constant in the raw prize-floor inequality is equivalent to a
uniform constant for the dimensionless Shaw value.  The same witness constant works in both
directions. -/
theorem shawFamilyBound_iff_prizeFamilyBound {ι : Type*} (M n m : ι → ℝ)
    (hn : ∀ i : ι, 0 < n i) (hm : ∀ i : ι, 1 < m i) :
    ShawFamilyBound M n m ↔ PrizeFamilyBound M n m := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    exact prizeScalarBound_of_shawValueBound (hn i) (hm i) (hC i)
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    exact shawValueBound_of_prizeScalarBound (hn i) (hm i) (hC i)

/-- Constant-preserving version of the family capstone. -/
theorem shawFamilyBound_with_constant_iff {ι : Type*} (C : ℝ) (M n m : ι → ℝ)
    (hn : ∀ i : ι, 0 < n i) (hm : ∀ i : ι, 1 < m i) :
    (∀ i : ι, ShawValueBound C (M i) (n i) (m i)) ↔
      (∀ i : ι, PrizeScalarBound C (M i) (n i) (m i)) := by
  constructor
  · intro h i
    exact prizeScalarBound_of_shawValueBound (hn i) (hm i) (h i)
  · intro h i
    exact shawValueBound_of_prizeScalarBound (hn i) (hm i) (h i)

end ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.prizeFloor_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.shawValueBound_iff_prizeScalarBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.shawFamilyBound_iff_prizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueScalarEquivalence.shawFamilyBound_with_constant_iff
