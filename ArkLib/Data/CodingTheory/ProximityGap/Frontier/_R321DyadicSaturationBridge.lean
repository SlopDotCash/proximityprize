/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.OrderOfElement

/-!
# R321: finite dyadic quotient implies dyadic saturation

The R321 recurrence census finds that the principal recurrence lattice sits inside the full
evaluation-kernel lattice with quotient cardinality `2^a` (`a <= 3` in all 92 hostile depth-4
cells).  This file records the abstract group-theoretic consequence: multiplying any relation
class by `2^a` kills the quotient, so every relation becomes recurrence-generated after that
dyadic scaling.

Issue #466, round 321.  The input identifying a concrete lattice quotient with the resultant
quotient remains separate.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R321DyadicSaturationBridge

/-- A finite additive quotient of cardinality `2^a` is annihilated by `2^a`. -/
theorem dyadic_nsmul_eq_zero {Q : Type*} [AddGroup Q] [Fintype Q]
    (a : ℕ) (hcard : Fintype.card Q = 2 ^ a) (q : Q) :
    (2 ^ a) • q = 0 := by
  rw [← hcard]
  exact card_nsmul_eq_zero

/-- Kernel form of dyadic saturation: if the target quotient has cardinality `2^a`, then
`2^a` times every source element lies in the kernel. -/
theorem dyadic_saturation_of_card_quotient {A Q : Type*} [AddGroup A] [AddGroup Q]
    [Fintype Q] (π : A →+ Q) (a : ℕ) (hcard : Fintype.card Q = 2 ^ a) (x : A) :
    (2 ^ a) • x ∈ π.ker := by
  rw [AddMonoidHom.mem_ker, map_nsmul, dyadic_nsmul_eq_zero a hcard]

/-- The concrete depth-4 census ceiling: quotient cardinality at most eight means eightfold
scaling always lands in the recurrence kernel. -/
theorem eight_saturation_of_card_dvd_eight {A Q : Type*} [AddGroup A] [AddCommGroup Q]
    [Fintype Q] (π : A →+ Q) (hcard : Fintype.card Q ∣ 8) (x : A) :
    8 • x ∈ π.ker := by
  rw [AddMonoidHom.mem_ker, map_nsmul]
  obtain ⟨k, hk⟩ := hcard
  rw [hk, mul_nsmul, card_nsmul_eq_zero, nsmul_zero]

#print axioms dyadic_nsmul_eq_zero
#print axioms dyadic_saturation_of_card_quotient
#print axioms eight_saturation_of_card_dvd_eight

end ArkLib.ProximityGap.Frontier.R321DyadicSaturationBridge
