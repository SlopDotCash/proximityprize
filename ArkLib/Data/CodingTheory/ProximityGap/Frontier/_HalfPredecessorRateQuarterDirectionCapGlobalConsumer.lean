/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterExceptionalDirectionPuncture

/-!
# Rate-quarter `n = 16`, `k = 4`: direction-cap global consumer

This file composes the exceptional-direction puncture with the exact global
core classification.  Every counterexample simultaneously has

* either the unique-eight-core residual or the no-eight-core intermediate
  residual; and
* one exceptional degree-`<4` direction core of size between six and
  thirteen, with a certified fresh full-agreement coordinate for every
  selected scalar.

This is a genuine sharpening of both core residuals, but not a closure.  The
current APIs impose no relation between the exceptional direction polynomial
and the slope of the residual source line.  Moreover, the trace lower bound
inside a direction core of size `z` is only `z-7`.  Throughout the surviving
band the constant-weight Plotkin gap fails:

```text
              (z - 7)^2 <= 3z,       6 <= z <= 13.
```

At `z=14` the inequality reverses (`49 > 42`), exactly explaining the
puncture module's sharp upper cutoff.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapDichotomy
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterExceptionalDirectionPuncture
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapGlobalConsumer

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The exceptional-direction package attached to every surviving core
residual. -/
def ExceptionalDirectionResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u) : Prop :=
  ∃ r : F[X], r.natDegree < 4 ∧
    6 ≤ (directionAgreement dom (u 1) r).card ∧
    (directionAgreement dom (u 1) r).card ≤ 13 ∧
    ∀ gamma ∈ family.G, ∃ i : I,
      i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
      i ∉ directionAgreement dom (u 1) r

/-- Wrapper exposing the exceptional-direction puncture in the residual
vocabulary used by the global consumer. -/
theorem card_le_sixteen_or_exceptionalDirectionResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9) :
    family.G.card ≤ 16 ∨ ExceptionalDirectionResidual family := by
  simpa only [ExceptionalDirectionResidual] using
    card_le_sixteen_or_exceptional_direction_core_band
      family hn hthreshold

/-- **Global composition.**  Every counterexample lies in one of the two
exact core residuals and simultaneously has an exceptional direction core in
the closed interval `[6,13]`. -/
theorem card_le_sixteen_or_coreResidual_and_exceptionalDirectionResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9) :
    family.G.card ≤ 16 ∨
      ((Nonempty (UniqueEightCoreResidual family) ∨
          Nonempty (NoEightCoreIntermediateResidual family)) ∧
        ExceptionalDirectionResidual family) := by
  rcases card_le_sixteen_or_unique_eight_core_or_no_eight_intermediate
      family hn hthreshold with hle | hhigh | hmid
  · exact Or.inl hle
  · rcases card_le_sixteen_or_exceptionalDirectionResidual
      family hn hthreshold with hle | hdir
    · exact Or.inl hle
    · exact Or.inr ⟨Or.inl hhigh, hdir⟩
  · rcases card_le_sixteen_or_exceptionalDirectionResidual
      family hn hthreshold with hle | hdir
    · exact Or.inl hle
    · exact Or.inr ⟨Or.inr hmid, hdir⟩

/-- The exact trace-weight Plotkin gap used by exceptional puncturing is
nonpositive throughout the surviving direction-core band. -/
theorem surviving_direction_band_plotkin_gap_fails
    {z : Nat} (hlower : 6 ≤ z) (hupper : z ≤ 13) :
    (z - 7) ^ 2 ≤ z * 3 := by
  interval_cases z <;> norm_num

/-- At the first excluded core size, the Plotkin gap is strictly positive. -/
theorem direction_core_fourteen_plotkin_gap_positive :
    14 * 3 < (14 - 7) ^ 2 := by
  norm_num

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapGlobalConsumer

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapGlobalConsumer
#print axioms card_le_sixteen_or_exceptionalDirectionResidual
#print axioms card_le_sixteen_or_coreResidual_and_exceptionalDirectionResidual
#print axioms surviving_direction_band_plotkin_gap_fails
#print axioms direction_core_fourteen_plotkin_gap_positive
