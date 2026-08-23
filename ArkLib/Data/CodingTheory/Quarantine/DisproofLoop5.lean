/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 5 — narrowing the correlation-disproof search to the Johnson→capacity band

Loop 4 killed every *list-size* explosion disproof (A1–A4) using the below-capacity dimension
wall. The remaining honest angle (O1 in `DISPROOF_LOG.md`) is to attack the MCA **correlation
probability** directly rather than the list size: a polynomially small list can in principle still
carry an anomalously large correlated-agreement probability.

But the correlation is *also* controlled in part of the radius range. Below the Johnson radius

    δ < 1 − √ρ,

Reed–Solomon list decoding is in the polynomial-list, unique-ish regime where the BCIKS20
proximity-gap theorem already gives the `poly/q` correlation bound. So any correlation-based
disproof must live strictly **above** the Johnson radius. Combined with the prize hypothesis
`δ ≤ 1 − ρ − η`, a disproof radius must satisfy

    1 − √ρ ≤ δ ≤ 1 − ρ − η.                                   (band)

This band is *non-empty only if* `η ≤ √ρ − ρ`. Since `√ρ − ρ = √ρ(1 − √ρ) > 0` for `0 < ρ < 1`,
the band is genuinely available — but only for sufficiently small gap `η`. Equivalently: whenever
the gap is large, `η > √ρ − ρ`, the *entire* prize radius range sits below the Johnson radius and
the conjecture's correlation bound holds for free. So any disproof attempt **must** fix
`η ≤ √ρ − ρ`; this is a hard narrowing of the search space, not a disproof.

This file proves the narrowing, sorry-free and axiom-clean. See `DISPROOF_LOG.md` (O1).
-/

namespace ArkLib.ProximityGap.DisproofLoop5

open scoped Real

/-- **The Johnson gap is strictly positive in the open unit interval.** For a rate `0 < ρ < 1`,
`√ρ − ρ > 0`, i.e. the Johnson radius `1 − √ρ` lies strictly below capacity `1 − ρ`. -/
theorem johnson_gap_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Real.sqrt ρ - ρ > 0 := by
  have hlt : ρ < Real.sqrt ρ := by
    -- `ρ = √ρ · √ρ < √ρ · 1 = √ρ` since `0 < √ρ < 1`.
    have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt (le_of_lt hρ0)
    have hspos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ0
    have hslt1 : Real.sqrt ρ < 1 := by
      have := Real.sqrt_lt_sqrt (le_of_lt hρ0) hρ1
      rwa [Real.sqrt_one] at this
    calc ρ = Real.sqrt ρ * Real.sqrt ρ := hsq.symm
      _ < Real.sqrt ρ * 1 := by exact (mul_lt_mul_of_pos_left hslt1 hspos)
      _ = Real.sqrt ρ := mul_one _
  linarith

/-- **The correlation-disproof band forces a small gap.** If a disproof radius `δ` lives above the
Johnson radius (`1 − √ρ ≤ δ`, where the proximity gap is no longer free) and also satisfies the
prize hypothesis (`δ ≤ 1 − ρ − η`), then the gap is constrained:

    η ≤ √ρ − ρ.

So no correlation-based disproof can use a gap larger than the Johnson gap `√ρ − ρ`. -/
theorem correlation_disproof_requires_small_gap
    {ρ η δ : ℝ}
    (hJohnson : 1 - Real.sqrt ρ ≤ δ)
    (hPrize : δ ≤ 1 - ρ - η) :
    η ≤ Real.sqrt ρ - ρ := by
  -- Chain the two radius bounds: `1 − √ρ ≤ δ ≤ 1 − ρ − η`.
  have h : 1 - Real.sqrt ρ ≤ 1 - ρ - η := le_trans hJohnson hPrize
  linarith

/-- **Contrapositive / "conjecture-holds-for-free" form.** If the gap exceeds the Johnson gap
(`η > √ρ − ρ`), then the prize radius range lies *entirely below* the Johnson radius: every
`δ ≤ 1 − ρ − η` satisfies `δ < 1 − √ρ`. In that whole regime the proximity-gap correlation bound
holds for free, so no disproof exists there. -/
theorem large_gap_forces_below_johnson
    {ρ η δ : ℝ}
    (hGap : Real.sqrt ρ - ρ < η)
    (hPrize : δ ≤ 1 - ρ - η) :
    δ < 1 - Real.sqrt ρ := by
  linarith

end ArkLib.ProximityGap.DisproofLoop5
