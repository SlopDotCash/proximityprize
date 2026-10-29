/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ArkLib.Data.Probability.Notation
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Uniform probability compatibility

Finite PMF sampling and VCVio's canonical sampler assign the same probability to every event.
The bridge lets downstream counting proofs reuse the authoritative native probability API.
-/

open ProbabilityTheory
open scoped ProbabilityTheory BigOperators

namespace ProximityPrize.Compatibility

/-- A finite PMF uniform sample assigns the accepted fraction of its outcomes to an event. -/
theorem pmf_uniform_probability_eq_card {α : Type} [Fintype α] [Nonempty α]
    (p : α → Prop) [DecidablePred p] :
    Pr_{let x ← $ᵖ α}[p x] =
      (Finset.univ.filter p).card / (Fintype.card α : ENNReal) := by
  classical
  rw [Pr_eq_tsum_indicator]
  simp only [uniformOfFintype_apply, tsum_fintype, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- PMF uniform sampling and the canonical native sampler agree on every finite event. -/
theorem pmf_uniform_probability_eq_native {α : Type} [Fintype α] [SampleableType α]
    (p : α → Prop) :
    Pr_{let x ← $ᵖ α}[p x] = Pr{let x ← $ᵗ α}[p x] := by
  classical
  rw [pmf_uniform_probability_eq_card, SampleableType.prEvent_uniformSample]

end ProximityPrize.Compatibility
