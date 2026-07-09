/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HigherOrderMDSReedSolomon
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The half-radius MDS line bound fails with strict slack and low rate

Take the nine Vandermonde parity columns

`v(x) = (1,x,x^2,...,x^6)`, for `x = 0,...,8`,

over `ZMod 11`.  They are the parity frame of a `[9,2]` Reed--Solomon code.  In
the seven-dimensional syndrome space, let `P` be the projective line with basis

```text
a = (1,4,0,2,8,10,6),   b = (1,8,6,5,7,7,7).
```

The nine affine representatives `a + gamma*b`, for
`gamma in {0,1,3,4,5,6,7,9,10}`, together with the point at infinity `b`, have
the displayed four-column decompositions below.  The ten supports are the
facets of two five-sets

```text
{0,3,5,6,7} and {0,1,2,4,8},
```

which overlap in one coordinate.  No displayed support contains the whole
projective line.  Thus the proper weight-four incidence is at least `10 > 9`.

This refutes the field-uniform line bound even with two units of strict slack
and in the low-rate range:

```text
2e = 8 < 9,   e+k+1 = 7 < 9,   k = 2 <= 9/4.
```

The construction is odd-length.  It does not refute the even, two-power
production slice `e=n/2-1`, where the analogous two disjoint half-blocks yield
exactly `n` facet points.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted

abbrev F := ZMod 11
abbrev V := Fin 7 -> F

/-- The nine distinct evaluation points `0,...,8` in `F_11`. -/
def domain : Fin 9 ↪ F where
  toFun x := x.val
  inj' := by decide

/-- A column of the seven-row Vandermonde parity frame. -/
def column (x : Fin 9) : V := fun j => domain x ^ (j : Nat)

/-- The first basis vector of the counterexample syndrome line. -/
def basePoint : V := ![1, 4, 0, 2, 8, 10, 6]

/-- The point at infinity, and second basis vector, of the syndrome line. -/
def directionPoint : V := ![1, 8, 6, 5, 7, 7, 7]

/-- A homogeneous representative of the vector plane under the projective line. -/
def lineVector (alpha beta : F) : V := fun j =>
  alpha * basePoint j + beta * directionPoint j

/-- The standard affine chart `a + gamma*b`. -/
def linePoint (gamma : F) : V := lineVector 1 gamma

/-- A displayed decomposition using four parity columns. -/
def fourColumnCertificate (u : V)
    (x0 x1 x2 x3 : Fin 9) (c0 c1 c2 c3 : F) : Prop :=
  u = fun j =>
    c0 * column x0 j + c1 * column x1 j +
      c2 * column x2 j + c3 * column x3 j

/-- Membership in one displayed four-column support span. -/
def inFourColumnSpan (u : V) (x0 x1 x2 x3 : Fin 9) : Prop :=
  exists c0 c1 c2 c3 : F, fourColumnCertificate u x0 x1 x2 x3 c0 c1 c2 c3

/-- The projective line is contained in a displayed support span. -/
def lineContainedInFourColumnSpan (x0 x1 x2 x3 : Fin 9) : Prop :=
  forall alpha beta : F, inFourColumnSpan (lineVector alpha beta) x0 x1 x2 x3

/-- A proper projective weight-four point on the fixed line. -/
def ProperLowWeightPoint (u : V) : Prop :=
  exists x0 x1 x2 x3 : Fin 9, exists c0 c1 c2 c3 : F,
    x0 ≠ x1 /\ x0 ≠ x2 /\ x0 ≠ x3 /\
    x1 ≠ x2 /\ x1 ≠ x3 /\ x2 ≠ x3 /\
    fourColumnCertificate u x0 x1 x2 x3 c0 c1 c2 c3 /\
    Not (lineContainedInFourColumnSpan x0 x1 x2 x3)

/-! ## The ten explicit four-column decompositions -/

theorem gamma_zero_certificate :
    fourColumnCertificate (linePoint 0) 0 3 6 7 4 9 5 5 := by
  funext j
  fin_cases j <;> decide

theorem gamma_one_certificate :
    fourColumnCertificate (linePoint 1) 0 3 5 7 4 7 6 7 := by
  funext j
  fin_cases j <;> decide

theorem gamma_three_certificate :
    fourColumnCertificate (linePoint 3) 0 3 5 6 4 3 7 1 := by
  funext j
  fin_cases j <;> decide

theorem gamma_four_certificate :
    fourColumnCertificate (linePoint 4) 0 2 4 8 9 3 6 9 := by
  funext j
  fin_cases j <;> decide

theorem gamma_five_certificate :
    fourColumnCertificate (linePoint 5) 0 1 4 8 6 3 3 5 := by
  funext j
  fin_cases j <;> decide

theorem gamma_six_certificate :
    fourColumnCertificate (linePoint 6) 0 1 2 8 3 6 8 1 := by
  funext j
  fin_cases j <;> decide

theorem gamma_seven_certificate :
    fourColumnCertificate (linePoint 7) 1 2 4 8 9 5 8 8 := by
  funext j
  fin_cases j <;> decide

theorem gamma_nine_certificate :
    fourColumnCertificate (linePoint 9) 0 1 2 4 5 4 10 2 := by
  funext j
  fin_cases j <;> decide

theorem gamma_ten_certificate :
    fourColumnCertificate (linePoint 10) 0 5 6 7 4 5 10 3 := by
  funext j
  fin_cases j <;> decide

theorem infinity_certificate :
    fourColumnCertificate directionPoint 3 5 6 7 9 6 6 2 := by
  funext j
  fin_cases j <;> decide

/-! ## Every displayed witness support is proper -/

theorem gamma_zero_support_proper :
    Not (lineContainedInFourColumnSpan 0 3 6 7) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_one_support_proper :
    Not (lineContainedInFourColumnSpan 0 3 5 7) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_three_support_proper :
    Not (lineContainedInFourColumnSpan 0 3 5 6) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_four_support_proper :
    Not (lineContainedInFourColumnSpan 0 2 4 8) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_five_support_proper :
    Not (lineContainedInFourColumnSpan 0 1 4 8) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_six_support_proper :
    Not (lineContainedInFourColumnSpan 0 1 2 8) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_seven_support_proper :
    Not (lineContainedInFourColumnSpan 1 2 4 8) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_nine_support_proper :
    Not (lineContainedInFourColumnSpan 0 1 2 4) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_ten_support_proper :
    Not (lineContainedInFourColumnSpan 0 5 6 7) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem infinity_support_proper :
    Not (lineContainedInFourColumnSpan 3 5 6 7) := by
  unfold lineContainedInFourColumnSpan inFourColumnSpan fourColumnCertificate
    lineVector basePoint directionPoint column domain
  decide

theorem gamma_zero_proper : ProperLowWeightPoint (linePoint 0) := by
  exact ⟨0, 3, 6, 7, 4, 9, 5, 5, by decide,
    gamma_zero_certificate, gamma_zero_support_proper⟩

theorem gamma_one_proper : ProperLowWeightPoint (linePoint 1) := by
  exact ⟨0, 3, 5, 7, 4, 7, 6, 7, by decide,
    gamma_one_certificate, gamma_one_support_proper⟩

theorem gamma_three_proper : ProperLowWeightPoint (linePoint 3) := by
  exact ⟨0, 3, 5, 6, 4, 3, 7, 1, by decide,
    gamma_three_certificate, gamma_three_support_proper⟩

theorem gamma_four_proper : ProperLowWeightPoint (linePoint 4) := by
  exact ⟨0, 2, 4, 8, 9, 3, 6, 9, by decide,
    gamma_four_certificate, gamma_four_support_proper⟩

theorem gamma_five_proper : ProperLowWeightPoint (linePoint 5) := by
  exact ⟨0, 1, 4, 8, 6, 3, 3, 5, by decide,
    gamma_five_certificate, gamma_five_support_proper⟩

theorem gamma_six_proper : ProperLowWeightPoint (linePoint 6) := by
  exact ⟨0, 1, 2, 8, 3, 6, 8, 1, by decide,
    gamma_six_certificate, gamma_six_support_proper⟩

theorem gamma_seven_proper : ProperLowWeightPoint (linePoint 7) := by
  exact ⟨1, 2, 4, 8, 9, 5, 8, 8, by decide,
    gamma_seven_certificate, gamma_seven_support_proper⟩

theorem gamma_nine_proper : ProperLowWeightPoint (linePoint 9) := by
  exact ⟨0, 1, 2, 4, 5, 4, 10, 2, by decide,
    gamma_nine_certificate, gamma_nine_support_proper⟩

theorem gamma_ten_proper : ProperLowWeightPoint (linePoint 10) := by
  exact ⟨0, 5, 6, 7, 4, 5, 10, 3, by decide,
    gamma_ten_certificate, gamma_ten_support_proper⟩

theorem infinity_proper : ProperLowWeightPoint directionPoint := by
  exact ⟨3, 5, 6, 7, 9, 6, 6, 2, by decide,
    infinity_certificate, infinity_support_proper⟩

/-! ## Projective distinctness and the incidence count -/

/-- Ten canonical representatives for the ten certified projective points. -/
def representative : Fin 10 -> V :=
  ![linePoint 0, linePoint 1, linePoint 3, linePoint 4, linePoint 5,
    linePoint 6, linePoint 7, linePoint 9, linePoint 10, directionPoint]

/-- Projective proportionality for nonzero representatives. -/
def Proportional (u v : V) : Prop :=
  exists c : F, c ≠ 0 /\ forall j, u j = c * v j

/-- The ten representatives are pairwise projectively inequivalent. -/
theorem representative_projectively_injective :
    forall i j : Fin 10,
      Proportional (representative i) (representative j) -> i = j := by
  unfold Proportional representative linePoint lineVector basePoint directionPoint
  decide

theorem every_representative_proper :
    forall i : Fin 10, ProperLowWeightPoint (representative i) := by
  intro i
  fin_cases i
  · exact gamma_zero_proper
  · exact gamma_one_proper
  · exact gamma_three_proper
  · exact gamma_four_proper
  · exact gamma_five_proper
  · exact gamma_six_proper
  · exact gamma_seven_proper
  · exact gamma_nine_proper
  · exact gamma_ten_proper
  · exact infinity_proper

/-- There are ten certified proper projective points, strictly more than the length. -/
theorem ten_gt_length : 9 < Fintype.card (Fin 10) := by decide

/-! ## Vandermonde MDS and numerical hypotheses -/

theorem domain_injective : Function.Injective domain := domain.injective

/-- Every set of at most seven parity columns is linearly independent. -/
theorem parityColumnsMDS (J : Finset (Fin 9)) (hJ : J.card <= 7) :
    LinearIndependent F (fun x : J => column x) := by
  exact ArkLib.HigherOrderMDS.rs_columns_linearIndependent domain.injective hJ

/-- The counterexample lies at the strict half-radius, two-slack, low-rate parameters. -/
theorem strict_low_rate_hypotheses :
    2 * 4 < 9 /\ 4 + 2 + 1 < 9 /\ 2 <= 9 / 4 := by
  decide

/-- Equivalent multiplication form of the low-rate condition `k <= n/4`. -/
theorem four_mul_dimension_le_length : 4 * 2 <= 9 := by decide

end ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted

#print axioms
  ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted.parityColumnsMDS
#print axioms
  ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted.representative_projectively_injective
#print axioms
  ArkLib.ProximityGap.Frontier.HalfRadiusStrictSlackLowRateRefuted.every_representative_proper
