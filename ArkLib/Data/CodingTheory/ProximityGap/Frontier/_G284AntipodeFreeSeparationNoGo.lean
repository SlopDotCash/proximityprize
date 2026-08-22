/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Prod
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# G284: antipode-free does not imply strict separation (#466)

G280 proved two facts about the live sponsor covariance. First, it is an odd real signed pairing:
`B(W, -R) = -B(W, R)`. Second, the finite family of recorded sponsor profiles is antipode-free:
no profile in the census is accompanied by its negative. This leaves an odd sponsor-specific
certificate algebraically possible, but it does not itself produce one.

The missing implication would be

```text
C ∩ (-C) = ∅  ->  exists ell and eta > 0, forall c in C, ell(c) >= eta.
```

It is false already for three points in dimension two. The set

```text
C = {(1,0), (0,1), (-1,-1)}
```

is antipode-free, but its three points sum to zero. Every linear functional therefore also sums to
zero on them, so it cannot be strictly positive on all three. Equivalently, zero lies in their
convex hull. The genuinely stronger geometric premise needed for a strict odd certificate is
`0 ∉ convexHull C`, together with a quantitative, independently specified separator.

This file proves the zero-sum obstruction abstractly and certifies the explicit antipode-free
countermodel over `ℚ²`. It does not deny that the actual sponsor family may admit an arithmetic
separator. It proves only that G280's antipode-free property supplies no separator or margin by
itself. CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G284AntipodeFreeSeparationNoGo

/-- No linear functional can be strictly positive on three vectors whose sum is zero. This is the
abstract obstruction behind the countermodel and is independent of dimension or depth. -/
theorem zero_sum_blocks_positive_linear_separator {V : Type*} [AddCommGroup V] [Module ℚ V]
    (a b c : V) (hsum : a + b + c = 0) :
    ¬ ∃ ell : V →ₗ[ℚ] ℚ, 0 < ell a ∧ 0 < ell b ∧ 0 < ell c := by
  rintro ⟨ell, ha, hb, hc⟩
  have hzero : ell a + ell b + ell c = 0 := by
    rw [← map_add, ← map_add, hsum, map_zero]
  linarith

/-- A finite set is antipode-free when it contains no vector together with its negative. -/
def AntipodeFree {V : Type*} [AddCommGroup V] [DecidableEq V] (C : Finset V) : Prop :=
  ∀ x ∈ C, -x ∉ C

/-- Strict separation of a finite rational vector set from zero by a positive linear margin. -/
def StrictlySeparated {V : Type*} [AddCommGroup V] [Module ℚ V] [DecidableEq V]
    (C : Finset V) : Prop :=
  ∃ (ell : V →ₗ[ℚ] ℚ) (eta : ℚ), 0 < eta ∧ ∀ x ∈ C, eta ≤ ell x

abbrev Point := ℚ × ℚ

/-- First vertex of the countermodel. -/
def pointA : Point := (1, 0)

/-- Second vertex of the countermodel. -/
def pointB : Point := (0, 1)

/-- Third vertex of the countermodel. -/
def pointC : Point := (-1, -1)

/-- The exact three-point countermodel `C = {(1,0),(0,1),(-1,-1)}`. -/
def countermodel : Finset Point := {pointA, pointB, pointC}

/-- The three vertices sum to zero. -/
theorem countermodel_sum_zero : pointA + pointB + pointC = 0 := by
  norm_num [pointA, pointB, pointC]

/-- The countermodel is antipode-free: none of its three vertices has its negative in the set. -/
theorem countermodel_antipodeFree : AntipodeFree countermodel := by
  norm_num [AntipodeFree, countermodel, pointA, pointB, pointC]

/-- Despite being antipode-free, the countermodel has no strict linear separator from zero. -/
theorem countermodel_not_strictlySeparated : ¬StrictlySeparated countermodel := by
  rintro ⟨ell, eta, heta, hmargin⟩
  have ha : eta ≤ ell pointA := hmargin pointA (by simp [countermodel])
  have hb : eta ≤ ell pointB := hmargin pointB (by simp [countermodel])
  have hc : eta ≤ ell pointC := hmargin pointC (by simp [countermodel])
  have hzero : ell pointA + ell pointB + ell pointC = 0 := by
    rw [← map_add, ← map_add, countermodel_sum_zero, map_zero]
  linarith

/-- **Antipode-freeness alone does not imply strict half-space separation.** This is the exact
countermodel to the tempting upgrade of G280's finite antipode census into an odd certificate. -/
theorem antipodeFree_not_imply_strictlySeparated :
    AntipodeFree countermodel ∧ ¬StrictlySeparated countermodel :=
  ⟨countermodel_antipodeFree, countermodel_not_strictlySeparated⟩

#print axioms zero_sum_blocks_positive_linear_separator
#print axioms countermodel_sum_zero
#print axioms countermodel_antipodeFree
#print axioms countermodel_not_strictlySeparated
#print axioms antipodeFree_not_imply_strictlySeparated

end ArkLib.ProximityGap.Frontier.G284AntipodeFreeSeparationNoGo
