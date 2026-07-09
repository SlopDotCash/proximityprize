/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# R383: the unrestricted half-radius MDS line conjecture is false

For the `[8,4]` Reed--Solomon syndrome geometry over `ZMod 17`, let

```text
v(x) = (1,x,x^2,x^3),        L(gamma) = (1,gamma,0,0).
```

The displayed certificates put nine distinct points of `L` in spans of three
columns `v(x)` with `x^8=1`.  In every certificate the base point `L(0)` is not
in the same span, so that support span does not contain the projective line.
Consequently the line has more than `n=8` proper weight-three points.

This refutes the field-uniform conjecture under its stated assumptions
`2e<n` and `e+k+1<=n`: here `(n,k,e)=(8,4,3)`.  It does not refute the
production-rate restriction `k<=n/4`, which remains the live half-radius target.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted

abbrev F := ZMod 17

/-- The projectively normalized parity-check column.  Nonzero GRS column
weights do not change any support span. -/
def column (x : F) : Fin 4 -> F := fun j => x ^ (j : Nat)

/-- The affine chart of the counterexample projective syndrome line. -/
def linePoint (gamma : F) : Fin 4 -> F := fun j =>
  if j = 0 then 1 else if j = 1 then gamma else 0

/-- A proper three-column certificate for one point of the syndrome line. -/
def properThreeColumnCertificate
    (gamma x y z a b c : F) : Prop :=
  x ^ 8 = 1 ∧ y ^ 8 = 1 ∧ z ^ 8 = 1 ∧
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
  linePoint gamma = a • column x + b • column y + c • column z

private theorem certificate_of_decide
    (gamma x y z a b c : F)
    (hroots : x ^ 8 = 1 ∧ y ^ 8 = 1 ∧ z ^ 8 = 1)
    (hdistinct : x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (hpoint : ∀ j, linePoint gamma j =
      (a • column x + b • column y + c • column z) j) :
    properThreeColumnCertificate gamma x y z a b c := by
  exact ⟨hroots.1, hroots.2.1, hroots.2.2,
    hdistinct.1, hdistinct.2.1, hdistinct.2.2, funext hpoint⟩

theorem gamma_one : properThreeColumnCertificate 1 1 9 8 11 2 5 := by
  apply certificate_of_decide <;> decide
theorem gamma_two : properThreeColumnCertificate 2 1 16 2 2 5 11 := by
  apply certificate_of_decide <;> decide
theorem gamma_three : properThreeColumnCertificate 3 1 4 2 8 13 14 := by
  apply certificate_of_decide <;> decide
theorem gamma_four : properThreeColumnCertificate 4 1 13 15 1 7 10 := by
  apply certificate_of_decide <;> decide
theorem gamma_five : properThreeColumnCertificate 5 1 9 13 13 14 8 := by
  apply certificate_of_decide <;> decide
theorem gamma_six : properThreeColumnCertificate 6 1 13 8 5 10 3 := by
  apply certificate_of_decide <;> decide
theorem gamma_seven : properThreeColumnCertificate 7 1 15 4 10 3 5 := by
  apply certificate_of_decide <;> decide
theorem gamma_eight : properThreeColumnCertificate 8 1 16 8 7 4 7 := by
  apply certificate_of_decide <;> decide
theorem gamma_nine : properThreeColumnCertificate 9 1 9 16 4 7 7 := by
  apply certificate_of_decide <;> decide

/-- The base point of the projective line is outside the span of any three
nonzero Vandermonde columns.  Pairing with
`(X-x)(X-y)(X-z)` leaves the nonzero constant term `-xyz`. -/
theorem linePoint_zero_not_mem_threeColumnSpan
    {x y z : F} (hxyz : x * y * z ≠ 0) :
    ¬ ∃ a b c : F,
      linePoint 0 = a • column x + b • column y + c • column z := by
  rintro ⟨a, b, c, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [linePoint, column] at h0 h1 h2 h3
  have hprod : x * y * z = 0 := by
    linear_combination
      -h3 + (x + y + z) * h2 - (x * y + x * z + y * z) * h1 + (x * y * z) * h0
  exact hxyz hprod

/-- A parameter has a proper weight-three witness on the fixed dyadic domain. -/
def ProperGamma (gamma : F) : Prop :=
  ∃ x y z a b c : F,
    properThreeColumnCertificate gamma x y z a b c ∧
    ¬ ∃ a' b' c' : F,
      linePoint 0 = a' • column x + b' • column y + c' • column z

private theorem properGamma_of_certificate
    {gamma x y z a b c : F}
    (hcert : properThreeColumnCertificate gamma x y z a b c)
    (hxyz : x * y * z ≠ 0) :
    ProperGamma gamma :=
  ⟨x, y, z, a, b, c, hcert,
    linePoint_zero_not_mem_threeColumnSpan hxyz⟩

/-- The nine certified affine parameters. -/
def certifiedGammas : Finset F := {1, 2, 3, 4, 5, 6, 7, 8, 9}

theorem certifiedGammas_card : certifiedGammas.card = 9 := by decide

theorem certifiedGammas_are_proper : ∀ gamma ∈ certifiedGammas, ProperGamma gamma := by
  intro gamma hgamma
  simp only [certifiedGammas, Finset.mem_insert, Finset.mem_singleton] at hgamma
  rcases hgamma with h | h | h | h | h | h | h | h | h
  · subst gamma
    exact properGamma_of_certificate gamma_one (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_two (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_three (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_four (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_five (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_six (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_seven (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_eight (by decide)
  · subst gamma
    exact properGamma_of_certificate gamma_nine (by decide)

/-- The unrestricted proposed ceiling `#proper points <= n` fails already at
`(n,k,e,q)=(8,4,3,17)`: this set contains nine distinct proper parameters. -/
theorem exists_more_than_eight_proper_points :
    ∃ G : Finset F, 8 < G.card ∧ ∀ gamma ∈ G, ProperGamma gamma := by
  refine ⟨certifiedGammas, ?_, certifiedGammas_are_proper⟩
  rw [certifiedGammas_card]
  omega

/-- The numerical hypotheses of the refuted conjecture are satisfied. -/
theorem conjecture_hypotheses_hold : 2 * 3 < 8 ∧ 3 + 4 + 1 ≤ 8 := by omega

end ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted

#print axioms ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted.gamma_one
#print axioms
  ArkLib.ProximityGap.Frontier.R383HalfRadiusMDSLineRefuted.exists_more_than_eight_proper_points
