/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import VCVio
import ToMathlib.MeasureTheory.Measure.IndependentDraws

/-!
# Distributional bind commutation

Independent oracle computations commute in their native evaluation measures. The canonical
VCVio proof supplies this fact without requiring measurable structures on intermediate outputs.
Independent native measure draws commute by `MeasureTheory.Measure.bind_bind_swap`; the
historical SPMF-specific name is retired. The generic measure law keeps its explicit s-finiteness
and joint measurability hypotheses.
-/

open MeasureTheory OracleComp

namespace OracleComp

/-- Independent uniform oracle computations commute in distribution. -/
theorem evalDist_bind_comm {ι : Type} {spec : OracleSpec ι}
    [OracleSpec.UniformAnswerMeasure spec]
    {α β γ : Type} [MeasurableSpace γ]
    (a : OracleComp spec α) (b : OracleComp spec β) (k : α → β → OracleComp spec γ) :
    𝒟[a >>= fun x => b >>= fun y => k x y] =
      𝒟[b >>= fun y => a >>= fun x => k x y] :=
  evalDist_bind_bind_swap_of_uniform a b k

end OracleComp
