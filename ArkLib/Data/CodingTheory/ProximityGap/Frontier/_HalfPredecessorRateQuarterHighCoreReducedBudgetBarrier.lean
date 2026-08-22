/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreCompleteResidual

/-!
# Rate-quarter high cores: reduced-budget barrier

The cap-`h-1` reduced-universe argument does not produce a second half core
on the globally surviving saturated high-core band.  Indeed, writing `h=2k`
and `z` for the source-core size, the band constraints

```text
2k <= z <= 3k-4
```

force the strict reverse of the required Rankin budget:

```text
(k+2)^2 - 1 < (4k-z)(2k-1).
```

For natural-number arithmetic, positivity of `k` is necessary: at the
truncated-subtraction endpoint `k=z=0`, both displayed band constraints hold
but the strict inequality does not.  Once `0 < k` is stated, the band itself
forces `4 <= k`; no stronger lower bound is needed.  This is a barrier theorem,
not a closure theorem: it explains why the first alternative of
`HighCoreCompleteResidual` is automatic on the nondegenerate global high-core
band and why a sharper petal cap or a different argument is needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnionSupply

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreReducedBudgetBarrier

attribute [local instance] Classical.propDecidable

/-- The nonempty saturated high-core band itself forces `k >= 4`. -/
theorem four_le_of_quarter_high_core_cap
    {k z : Nat} (hkpos : 0 < k) (hhigh : 2 * k ≤ z)
    (hcap : z ≤ 3 * k - 4) :
    4 ≤ k := by
  omega

/-- **Exact reduced-budget barrier.**  Throughout the saturated high-core
band, the cap-`h-1` Rankin budget fails strictly. -/
theorem quarter_high_core_cap_forces_reduced_budget_failure
    {k z : Nat} (hkpos : 0 < k) (hhigh : 2 * k ≤ z)
    (hcap : z ≤ 3 * k - 4) :
    (k + 2) ^ 2 - 1 < (4 * k - z) * (2 * k - 1) := by
  have hk : 4 ≤ k := four_le_of_quarter_high_core_cap hkpos hhigh hcap
  have hfirst : k + 2 ≤ k + 4 := by omega
  have hsecond : k + 2 ≤ 2 * k - 1 := by omega
  have hcomplement : k + 4 ≤ 4 * k - z := by omega
  have hpositive : 0 < (k + 2) ^ 2 := by positivity
  have hstrict : (k + 2) ^ 2 - 1 < (k + 2) ^ 2 := by omega
  have hsquare : (k + 2) ^ 2 ≤ (k + 4) * (2 * k - 1) := by
    rw [pow_two]
    exact Nat.mul_le_mul hfirst hsecond
  have hlast : (k + 4) * (2 * k - 1) ≤
      (4 * k - z) * (2 * k - 1) :=
    Nat.mul_le_mul_right (2 * k - 1) hcomplement
  exact hstrict.trans_le (hsquare.trans hlast)

/-- The same barrier in the exact variables used by the high-core petal
growth API. -/
theorem saturated_high_core_cap_forces_reduced_budget_failure
    {k h z : Nat} (hkpos : 0 < k) (hsaturated : h = 2 * k)
    (hhigh : h ≤ z) (hcap : z ≤ 3 * k - 4) :
    (h + 1 - (k - 1)) ^ 2 - 1 < (2 * h - z) * (h - 1) := by
  have hbase := quarter_high_core_cap_forces_reduced_budget_failure
    (k := k) (z := z) hkpos (by omega) hcap
  have hleft : h + 1 - (k - 1) = k + 2 := by omega
  have hcomplement : 2 * h - z = 4 * k - z := by omega
  have hpred : h - 1 = 2 * k - 1 := by omega
  rw [hleft, hcomplement, hpred]
  exact hbase

/-- Equivalently, the sufficient reduced-budget hypothesis used to force a
second half core is false on this band. -/
theorem not_reduced_budget_of_saturated_high_core_cap
    {k h z : Nat} (hkpos : 0 < k) (hsaturated : h = 2 * k)
    (hhigh : h ≤ z) (hcap : z ≤ 3 * k - 4) :
    ¬ (2 * h - z) * (h - 1) ≤ (h + 1 - (k - 1)) ^ 2 - 1 := by
  intro hbudget
  have hfailure := saturated_high_core_cap_forces_reduced_budget_failure
    hkpos hsaturated hhigh hcap
  omega

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Family-level barrier form.**  A relevant high core in the global
surviving band automatically realizes the reduced-budget-failure alternative
of the complete residual theorem. -/
theorem relevant_high_core_reduced_budget_failure_of_global_cap
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hkpos : 0 < k) (hsaturated : h = 2 * k) (line : LineParameter F)
    (hline : line ∈ highCoreLines family h)
    (hcap :
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4) :
    (h + 1 - (k - 1)) ^ 2 - 1 <
      (2 * h -
        (jointCore dom (u 0) (u 1) line.1 line.2).card) * (h - 1) := by
  have hhigh := (mem_highCoreLines_iff family h line).mp hline |>.2
  exact saturated_high_core_cap_forces_reduced_budget_failure
    hkpos hsaturated hhigh hcap

/-- The actual second-core budget premise is unavailable for a relevant high
core satisfying the global `3k-4` ceiling. -/
theorem relevant_high_core_not_reduced_budget_of_global_cap
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hkpos : 0 < k) (hsaturated : h = 2 * k) (line : LineParameter F)
    (hline : line ∈ highCoreLines family h)
    (hcap :
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4) :
    ¬ (2 * h -
        (jointCore dom (u 0) (u 1) line.1 line.2).card) * (h - 1) ≤
      (h + 1 - (k - 1)) ^ 2 - 1 := by
  intro hbudget
  have hfailure := relevant_high_core_reduced_budget_failure_of_global_cap
    family hkpos hsaturated line hline hcap
  omega

#print axioms quarter_high_core_cap_forces_reduced_budget_failure
#print axioms saturated_high_core_cap_forces_reduced_budget_failure
#print axioms relevant_high_core_reduced_budget_failure_of_global_cap
#print axioms relevant_high_core_not_reduced_budget_of_global_cap

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreReducedBudgetBarrier
