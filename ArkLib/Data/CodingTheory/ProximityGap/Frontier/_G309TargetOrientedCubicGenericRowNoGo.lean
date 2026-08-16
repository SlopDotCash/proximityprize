/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# G309: the target-oriented odd cubic normal needs genuine rank-row structure

At the second certified sponsor, the coefficient class `[2]` generates the quotient and its odd
order is divisible by three. This canonically orients the inversion-odd cubic normal

```text
L3odd(R) = sum_j s3(j) A_[2]^j(R),
s3(j) = 0, +1, -1 according as j = 0, 1, 2 mod 3.
```

The exact rank-five/rank-six census leaves the one-sided implication
`L3odd(R_r) > 0 -> A_2(R_r) > 0` unrefuted for actual adjacent-rank subset-sum rows. This file
proves the sharp scope fence: that implication is false for arbitrary nonnegative rows, even on the
proper dyadic subgroup
`mu_8 <= F_73^*` where `[2]` generates the nine-element quotient.

For the nonnegative delta row `R = 1_{4}`, the nine quotient alignments are exactly

```text
(-64, -64, -64, 9, 82, 9, -64, 82, 82).
```

Hence the coefficient-two target is `A_2(R) = -64`, while `L3odd(R) = 73`. The countermodel is
independent of any rank parameter: it excludes every proof that uses only row nonnegativity and the
odd-cubic quotient weights. Any surviving transfer must exploit additional structure of the actual
subset-sum row. This is a route delimiter, not a production sign theorem and not prize closure.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace ArkLib.ProximityGap.Frontier.G309TargetOrientedCubicGenericRowNoGo

open Finset

/-- The proper order-eight dyadic subgroup `mu_8 <= F_73^*`, represented as a residue finset. -/
def H73 : Finset (ZMod 73) := {1, 10, 22, 27, 46, 51, 63, 72}

/-- The coefficient-`a` weighted relation profile on the explicit subgroup `H73`. -/
def weightedKernel73 (a t : ZMod 73) : ℤ :=
  ∑ y ∈ H73, ∑ z ∈ H73, if a * y - z = t then 1 else 0

/-- The centered coefficient alignment against an arbitrary integer row. -/
def anchorAlignment73 (R : ZMod 73 → ℤ) (a : ZMod 73) : ℤ :=
  73 * ∑ t : ZMod 73, weightedKernel73 a t * R t - 64 * ∑ t : ZMod 73, R t

/-- The quotient classes labelled by powers `[2]^j`, `j in Z/9Z`. -/
def quotientCoeff : Fin 9 → ZMod 73 := ![1, 2, 4, 8, 16, 32, 64, 55, 37]

/-- The target-oriented odd cubic weight `s3 = (0,+1,-1)` modulo three. -/
def oddCubicWeight : Fin 9 → ℤ := ![0, 1, -1, 0, 1, -1, 0, 1, -1]

/-- The target-oriented odd cubic quotient normal of a row. -/
def oddCubicNormal (R : ZMod 73 → ℤ) : ℤ :=
  ∑ j, oddCubicWeight j * anchorAlignment73 R (quotientCoeff j)

/-- The nonnegative delta row concentrated at residue four. -/
def deltaRow : ZMod 73 → ℤ := fun t => if t = 4 then 1 else 0

/-- The countermodel row is pointwise nonnegative. -/
theorem deltaRow_nonnegative (t : ZMod 73) : 0 ≤ deltaRow t := by
  by_cases h : t = 4 <;> simp [deltaRow, h]

/-- The delta row has total mass one. -/
theorem deltaRow_sum : ∑ t : ZMod 73, deltaRow t = 1 := by
  simp [deltaRow]

/-- Pairing any kernel against the delta row selects its value at residue four. -/
theorem weightedKernel73_dot_deltaRow (a : ZMod 73) :
    ∑ t : ZMod 73, weightedKernel73 a t * deltaRow t = weightedKernel73 a 4 := by
  classical
  simp [deltaRow]

/-- The nine exact kernel multiplicities at residue four. -/
theorem deltaRow_kernel_profile :
    (fun j => weightedKernel73 (quotientCoeff j) 4) = ![0, 0, 0, 1, 2, 1, 0, 2, 2] := by
  funext j
  fin_cases j <;> decide

/-- Exact quotient-alignment profile of the delta row. -/
theorem deltaRow_alignment_profile :
    (fun j => anchorAlignment73 deltaRow (quotientCoeff j)) =
      ![-64, -64, -64, 9, 82, 9, -64, 82, 82] := by
  funext j
  rw [anchorAlignment73, weightedKernel73_dot_deltaRow, deltaRow_sum]
  have h := congrFun deltaRow_kernel_profile j
  fin_cases j <;> simp_all [quotientCoeff]

/-- The coefficient-two target alignment is strictly negative. -/
theorem deltaRow_target_negative : anchorAlignment73 deltaRow 2 = -64 := by
  have h := congrFun deltaRow_alignment_profile (1 : Fin 9)
  simpa [quotientCoeff] using h

/-- The target-oriented odd cubic normal is strictly positive. -/
theorem deltaRow_oddCubic_positive : oddCubicNormal deltaRow = 73 := by
  rw [oddCubicNormal]
  simp_rw [congrFun deltaRow_alignment_profile]
  decide

/-- A generic transfer principle that uses only nonnegativity of the row. -/
def GenericOddCubicTransfer : Prop :=
  ∀ R : ZMod 73 → ℤ,
    (∀ t, 0 ≤ R t) → 0 < oddCubicNormal R → 0 < anchorAlignment73 R 2

/-- **Scope fence.** The odd cubic implication cannot follow from row nonnegativity alone. The
countermodel is depth-independent, so any valid transfer for adjacent-rank rows must use their
additional subset-sum structure. -/
theorem not_genericOddCubicTransfer : ¬ GenericOddCubicTransfer := by
  intro h
  have htarget := h deltaRow deltaRow_nonnegative (by rw [deltaRow_oddCubic_positive]; norm_num)
  rw [deltaRow_target_negative] at htarget
  norm_num at htarget

/-- Calibrated existential form of the same obstruction. -/
theorem nonnegative_row_with_positive_oddCubic_and_negative_target :
    ∃ R : ZMod 73 → ℤ,
      (∀ t, 0 ≤ R t) ∧ 0 < oddCubicNormal R ∧ anchorAlignment73 R 2 < 0 := by
  refine ⟨deltaRow, deltaRow_nonnegative, ?_, ?_⟩
  · rw [deltaRow_oddCubic_positive]
    norm_num
  · rw [deltaRow_target_negative]
    norm_num

#print axioms deltaRow_nonnegative
#print axioms deltaRow_alignment_profile
#print axioms deltaRow_target_negative
#print axioms deltaRow_oddCubic_positive
#print axioms not_genericOddCubicTransfer
#print axioms nonnegative_row_with_positive_oddCubic_and_negative_target

end ArkLib.ProximityGap.Frontier.G309TargetOrientedCubicGenericRowNoGo
